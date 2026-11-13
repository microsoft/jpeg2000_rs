use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_reservation_result(old(values)@, final(values)@, result),
))]
fn reserve_additional<T>(values: &mut Vec<T>, additional: usize) -> Result<(), DecodeError> {
    #[cfg(test)]
    if core::mem::size_of::<T>() != 0 && additional > values.capacity().saturating_sub(values.len())
    {
        refuse_managed_request()?;
    }
    match values.try_reserve(additional) {
        Ok(()) => Ok(()),
        Err(_) => Err(DecodeError::AllocationFailed),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_capacity_result(result),
))]
pub(crate) fn empty_with_capacity<T>(capacity: usize) -> Result<Vec<T>, DecodeError> {
    let mut values = Vec::new();
    reserve_additional(&mut values, capacity)?;
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_extension_result(
        old(values)@, bytes@, final(values)@, result),
))]
pub(crate) fn extend_bytes(values: &mut Vec<u8>, bytes: &[u8]) -> Result<(), DecodeError> {
    if bytes.is_empty() {
        return Ok(());
    }
    reserve_additional(values, bytes.len())?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost previous = values@; }
    values.extend_from_slice(bytes);
    #[cfg(verus_keep_ghost)]
    proof! { assert(values@ =~= previous + bytes@); }
    Ok(())
}

#[cfg(test)]
std::thread_local! {
    static REFUSAL: core::cell::Cell<Option<usize>> = const {
        core::cell::Cell::new(None)
    };
}

#[cfg(test)]
fn refuse_managed_request() -> Result<(), DecodeError> {
    REFUSAL.with(|remaining| match remaining.get() {
        None => Ok(()),
        Some(0) => {
            remaining.set(None);
            Err(DecodeError::AllocationFailed)
        }
        Some(count) => {
            remaining.set(Some(count - 1));
            Ok(())
        }
    })
}

#[cfg(test)]
pub(crate) fn with_refusal<T>(after: usize, operation: impl FnOnce() -> T) -> T {
    struct Restore(Option<usize>);

    impl Drop for Restore {
        fn drop(&mut self) {
            REFUSAL.with(|remaining| remaining.set(self.0));
        }
    }

    let _restore = Restore(REFUSAL.with(|remaining| remaining.replace(Some(after))));
    operation()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capacity_refusal_and_layout_overflow_return_typed_errors_and_recover() {
        assert_eq!(
            with_refusal(0, || empty_with_capacity::<u8>(8)),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(
            empty_with_capacity::<u64>(usize::MAX),
            Err(DecodeError::AllocationFailed)
        );
        let recovered = empty_with_capacity::<u8>(8).unwrap();
        assert!(recovered.is_empty());
        assert!(recovered.capacity() >= 8);
        with_refusal(0, || {
            assert!(empty_with_capacity::<u8>(0).unwrap().is_empty());
            assert!(empty_with_capacity::<()>(8).unwrap().is_empty());
            assert_eq!(
                empty_with_capacity::<u8>(8),
                Err(DecodeError::AllocationFailed)
            );
        });
    }

    #[test]
    fn byte_extension_refusal_preserves_values_and_owner_then_recovers() {
        let mut values = vec![7, 8, 9];
        let bytes = vec![4; values.capacity() + 1];
        let before = values.clone();
        let owner = (values.as_ptr(), values.len(), values.capacity());
        assert_eq!(
            with_refusal(0, || {
                assert_eq!(extend_bytes(&mut values, &[]), Ok(()));
                assert_eq!((values.as_ptr(), values.len(), values.capacity()), owner);
                extend_bytes(&mut values, &bytes)
            }),
            Err(DecodeError::AllocationFailed)
        );
        assert_eq!(values, before);
        assert_eq!((values.as_ptr(), values.len(), values.capacity()), owner);
        extend_bytes(&mut values, &bytes).unwrap();
        assert_eq!(values, [before, bytes].concat());
    }
}
