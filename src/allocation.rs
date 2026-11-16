use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub(crate) enum InspectionCollection {
    Infos(bool),
    Layers,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn inspection_capacity_outcome<T>(result: Result<T, DecodeError>) -> Result<(), DecodeError> {
        match result { Err(error) => Err(error), Ok(_) => Ok(()) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_inspection_capacity_result(_collection, count, inspection_capacity_outcome(result)),
        match result { Ok(values) => values@.len() == 0, Err(error) => error == DecodeError::AllocationFailed },
))]
pub(crate) fn inspection_values<T>(
    count: usize,
    _collection: InspectionCollection,
) -> Result<Vec<T>, DecodeError> {
    let result = if count == 0 {
        Ok(Vec::new())
    } else {
        empty_with_capacity(count)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_inspection_capacity_observed(_collection, count, inspection_capacity_outcome(result));
    }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_reservation_result(old(values)@, final(values)@, result),
))]
fn reserve_additional<T>(values: &mut Vec<T>, additional: usize) -> Result<(), DecodeError> {
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(test)]
    if core::mem::size_of::<T>() != 0 && additional > values.capacity().saturating_sub(values.len())
    {
        refuse_managed_request()?;
    }
    let result = match values.try_reserve(additional) {
        Ok(()) => Ok(()),
        Err(_) => Err(DecodeError::AllocationFailed),
    };
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    result
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
    ensures crate::specs::storage_copy_result(Seq::new(count as nat, |_: int| 0i64), result),
        count == 0 ==> result.is_ok(),
))]
pub(crate) fn zero_i64_values(count: usize) -> Result<Vec<i64>, DecodeError> {
    if count == 0 {
        #[cfg(verus_keep_ghost)]
        proof! {assert(Seq::<i64>::empty() =~= Seq::new(0nat,|_:int|0i64));}
        return Ok(Vec::new());
    }
    let mut values = empty_with_capacity(count)?;
    values.resize(count, 0_i64);
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<count implies values@[i]==0i64 by {
            assert(vstd::pervasive::cloned::<i64>(0i64,values@[i]));
        }
        assert(values@ =~= Seq::new(count as nat,|_:int|0i64));
    }
    Ok(values)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_copy_result(source@, result),
))]
pub(crate) fn copy_i64_values(source: &[i64]) -> Result<Vec<i64>, DecodeError> {
    if source.is_empty() {
        #[cfg(verus_keep_ghost)]
        proof! {assert(source@ =~= Seq::<i64>::empty());}
        return Ok(Vec::new());
    }
    let mut values = empty_with_capacity(source.len())?;
    values.extend_from_slice(source);
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:int|0<=i<source.len() implies values@[i]==source@[i] by {
            assert(vstd::pervasive::cloned::<i64>(source@[i],values@[i]));
        }
        assert(values@ =~= source@);
    }
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
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(values.len())?;
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
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
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
    ensures crate::specs::storage_copy_result(Seq::new(count as nat, |_: int| value), result),
        count == 0 ==> result.is_ok(),
        match result { Ok(values) => values@ == Seq::new(count as nat, |_: int| value),
            Err(error) => error == DecodeError::AllocationFailed },
))]
pub(crate) fn filled_values<T: Copy>(value: T, count: usize) -> Result<Vec<T>, DecodeError> {
    if count == 0 {
        #[cfg(verus_keep_ghost)]
        proof! { assert(Seq::<T>::empty() =~= Seq::new(0nat, |_: int| value)); }
        return Ok(Vec::new());
    }
    let mut values = empty_with_capacity(count)?;
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count, values@ == Seq::new(index as nat, |_: int| value),
        decreases count - index,
    ))]
    while index < count {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        values.push(value);
        #[cfg(verus_keep_ghost)]
        proof! { assert(Seq::new(index as nat + 1, |_: int| value) =~= Seq::new(index as nat, |_: int| value).push(value)); }
        index += 1;
    }
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
    #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
    crate::deadline::checkpoint()?;
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
    #[test]
    fn bulk_i64_copy_preserves_raw_empty_prior_owner_first_later_and_restore() {
        use super::{copy_i64_values, with_refusal};
        use crate::DecodeError;
        let source = [i64::MIN, 7, -1, 0, i64::MAX];
        with_refusal(0, || {
            assert_eq!(copy_i64_values(&[]).unwrap(), []);
            assert_eq!(copy_i64_values(&source), Err(DecodeError::AllocationFailed));
            assert_eq!(copy_i64_values(&source).unwrap(), source);
        });
        with_refusal(1, || {
            let prior = copy_i64_values(&source).unwrap();
            assert_eq!(copy_i64_values(&source), Err(DecodeError::AllocationFailed));
            assert_eq!(prior, source);
            assert_eq!(copy_i64_values(&source).unwrap(), source);
        });
        assert_eq!(source, [i64::MIN, 7, -1, 0, i64::MAX]);
    }

    use super::*;

    #[test]
    fn bulk_zero_i64_empty_first_later_refusal_and_restore_keep_exact_values() {
        with_refusal(0, || {
            assert!(zero_i64_values(0).unwrap().is_empty());
            assert_eq!(zero_i64_values(3), Err(DecodeError::AllocationFailed));
            assert_eq!(zero_i64_values(3).unwrap(), [0; 3]);
        });
        with_refusal(1, || {
            let prior = zero_i64_values(17).unwrap();
            assert_eq!(zero_i64_values(3), Err(DecodeError::AllocationFailed));
            assert_eq!(prior, [0; 17]);
            assert_eq!(zero_i64_values(3).unwrap(), [0; 3]);
        });
    }

    #[test]
    fn preparation_fill_zero_refusal_and_restore_keep_exact_values() {
        with_refusal(0, || {
            assert!(filled_values(false, 0).unwrap().is_empty());
            assert_eq!(filled_values(false, 3), Err(DecodeError::AllocationFailed));
        });
        assert_eq!(filled_values(7_u8, 3).unwrap(), [7, 7, 7]);
    }

    #[test]
    fn fresh_inspection_empty_roles_do_not_consume_refusal_and_restore() {
        struct NonClone {
            _byte: u8,
        }
        with_refusal(0, || {
            assert!(
                inspection_values::<NonClone>(0, InspectionCollection::Infos(false))
                    .unwrap()
                    .is_empty()
            );
            assert!(
                inspection_values::<NonClone>(0, InspectionCollection::Infos(true))
                    .unwrap()
                    .is_empty()
            );
            assert!(
                inspection_values::<NonClone>(0, InspectionCollection::Layers)
                    .unwrap()
                    .is_empty()
            );
            assert!(matches!(
                inspection_values::<NonClone>(1, InspectionCollection::Layers),
                Err(DecodeError::AllocationFailed)
            ));
        });
        assert!(
            inspection_values::<NonClone>(2, InspectionCollection::Infos(false))
                .unwrap()
                .is_empty()
        );
    }

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
