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
    ensures crate::specs::storage_none_result(count, result),
))]
pub(crate) fn none_values<T>(count: usize) -> Result<Vec<Option<T>>, DecodeError> {
    let mut values = empty_with_capacity(count)?;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant values.len() <= count,
            values@ == Seq::<Option<T>>::new(values.len() as nat, |_: int| None),
        decreases count - values.len(),
    ))]
    while values.len() < count {
        values.push(None);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(values@ =~= Seq::<Option<T>>::new(values.len() as nat, |_: int| None));
        }
    }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_copy_result(source@, result),
))]
pub(crate) fn copy_values<T: Copy>(source: &[T]) -> Result<Vec<T>, DecodeError> {
    if source.is_empty() {
        #[cfg(verus_keep_ghost)]
        proof! { assert(source@ =~= Seq::<T>::empty()); }
        return Ok(Vec::new());
    }
    let mut values = empty_with_capacity(source.len())?;
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= source.len(),
            values@ == source@.take(index as int),
        decreases source.len() - index,
    ))]
    while index < source.len() {
        values.push(source[index]);
        index += 1;
        #[cfg(verus_keep_ghost)]
        proof! { assert(values@ =~= source@.take(index as int)); }
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(values@ =~= source@); }
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
    fn shallow_copy_refusal_preserves_source_and_restores_exact_values() {
        let source = [3_u16, 5, 8];
        with_refusal(0, || {
            assert!(copy_values::<u16>(&[]).unwrap().is_empty());
            assert_eq!(copy_values(&source), Err(DecodeError::AllocationFailed));
            assert_eq!(source, [3, 5, 8]);
            assert_eq!(copy_values(&source).unwrap(), source);
        });
        assert_eq!(copy_values(&source).unwrap(), source);
    }

    #[test]
    fn none_storage_refuses_once_without_requiring_clone_and_restores() {
        struct NotClone;

        with_refusal(0, || {
            assert!(none_values::<NotClone>(0).unwrap().is_empty());
            assert!(matches!(
                none_values::<NotClone>(2),
                Err(DecodeError::AllocationFailed)
            ));
        });
        let restored = none_values::<NotClone>(2).unwrap();
        assert_eq!(restored.len(), 2);
        assert!(restored.iter().all(Option::is_none));
        assert!(matches!(
            none_values::<NotClone>(usize::MAX),
            Err(DecodeError::AllocationFailed)
        ));
    }

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
