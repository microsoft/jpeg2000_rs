use crate::DecodeError;
use std::cell::Cell;
use std::time::Instant;

std::thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

/// Run synchronous work under a caller-selected cooperative deadline.
///
/// Available with the native-only `cooperative-deadlines` feature. Nested scopes
/// retain the earliest deadline. Entry and exit are checked, including after an
/// operation returns an error; expiry at the exit checkpoint takes precedence.
/// Prior state is restored on every return and during native Rust unwinding.
///
/// Checkpoints do not preempt a thread, interrupt host work or propagate into a
/// different thread. No hard wall-clock guarantee is made. Clock/TLS effects are
/// outside the pinned Verus profile; the unsupported combined profile is rejected.
pub fn with_decode_deadline<T>(
    deadline: Instant,
    operation: impl FnOnce() -> Result<T, DecodeError>,
) -> Result<T, DecodeError> {
    let parent = DEADLINE.with(Cell::get);
    let effective = match parent {
        None => deadline,
        Some(parent) => parent.min(deadline),
    };
    DEADLINE.with(|current| current.set(Some(effective)));
    let _scope = Restore(parent);
    checkpoint()?;
    let result = operation();
    checkpoint()?;
    result
}

struct Restore(Option<Instant>);

impl Drop for Restore {
    fn drop(&mut self) {
        DEADLINE.with(|current| current.set(self.0));
    }
}

pub(crate) fn checkpoint() -> Result<(), DecodeError> {
    DEADLINE.with(|current| match current.get() {
        Some(deadline) if Instant::now() >= deadline => Err(DecodeError::DeadlineExceeded),
        _ => Ok(()),
    })
}

#[inline]
pub(crate) fn checkpoint_periodic(progress: usize) -> Result<(), DecodeError> {
    if progress & 1023 == 0 {
        checkpoint()
    } else {
        Ok(())
    }
}

#[inline]
pub(crate) fn checkpoint_work(progress: u64, increment: u64) -> Result<(), DecodeError> {
    if progress == 0 || increment >= 1024 || (progress & 1023) + increment >= 1024 {
        checkpoint()
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn expired_deadline_rejects_before_work_and_restores_scope() {
        let called = Cell::new(false);
        assert_eq!(
            with_decode_deadline(Instant::now(), || {
                called.set(true);
                Ok(())
            }),
            Err(DecodeError::DeadlineExceeded),
        );
        assert!(!called.get());
        assert!(crate::allocation::empty_with_capacity::<u8>(8).is_ok());
        let error = DecodeError::MalformedInput {
            offset: 7,
            kind: crate::MalformedKind::Truncated,
        };
        assert_eq!(
            with_decode_deadline(Instant::now() + Duration::from_secs(60), || Err::<(), _>(
                error
            )),
            Err(error),
        );
        assert!(checkpoint().is_ok());
    }

    #[test]
    fn deadline_expiring_during_work_precedes_managed_allocation_failure() {
        let result = with_decode_deadline(Instant::now() + Duration::from_millis(5), || {
            std::thread::sleep(Duration::from_millis(15));
            crate::allocation::empty_with_capacity::<u8>(usize::MAX)
        });
        assert_eq!(result, Err(DecodeError::DeadlineExceeded));
        assert_eq!(
            crate::allocation::with_refusal(0, || crate::allocation::empty_with_capacity::<u8>(8)),
            Err(DecodeError::AllocationFailed),
        );
        assert!(crate::allocation::empty_with_capacity::<u8>(8).is_ok());
    }

    #[test]
    fn nested_scope_cannot_extend_parent_and_restores_each_scope() {
        let parent = Instant::now() + Duration::from_secs(60);
        with_decode_deadline(parent, || {
            assert_eq!(DEADLINE.with(Cell::get), Some(parent));
            with_decode_deadline(parent + Duration::from_secs(60), || {
                assert_eq!(DEADLINE.with(Cell::get), Some(parent));
                Ok(())
            })?;
            let earlier = Instant::now() + Duration::from_secs(30);
            with_decode_deadline(earlier, || {
                assert_eq!(DEADLINE.with(Cell::get), Some(earlier));
                Ok(())
            })?;
            assert_eq!(DEADLINE.with(Cell::get), Some(parent));
            Ok(())
        })
        .unwrap();
        assert!(DEADLINE.with(Cell::get).is_none());
    }

    #[test]
    fn unwind_and_separate_threads_do_not_leak_deadlines() {
        let panic = std::panic::catch_unwind(|| {
            let _ = with_decode_deadline(
                Instant::now() + Duration::from_secs(60),
                || -> Result<(), DecodeError> {
                    panic!("scope restoration control");
                },
            );
        });
        assert!(panic.is_err());
        assert!(DEADLINE.with(Cell::get).is_none());
        let expired = with_decode_deadline(Instant::now() + Duration::from_millis(5), || {
            std::thread::sleep(Duration::from_millis(15));
            std::thread::spawn(|| {
                assert!(DEADLINE.with(Cell::get).is_none());
                crate::allocation::empty_with_capacity::<u8>(8)
            })
            .join()
            .unwrap()
        });
        assert_eq!(expired, Err(DecodeError::DeadlineExceeded));
        assert!(crate::allocation::empty_with_capacity::<u8>(8).is_ok());
    }
}
