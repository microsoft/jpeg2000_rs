use crate::DecodeError;
use vstd::prelude::*;

verus! {

pub open spec fn storage_reservation_result<T>(
    before: Seq<T>, after: Seq<T>, result: Result<(), DecodeError>,
) -> bool {
    after == before && match result {
        Ok(()) => true,
        Err(error) => error == DecodeError::AllocationFailed,
    }
}

pub open spec fn storage_capacity_result<T>(result: Result<Vec<T>, DecodeError>) -> bool {
    match result {
        Ok(values) => values@ == Seq::<T>::empty(),
        Err(error) => error == DecodeError::AllocationFailed,
    }
}

pub open spec fn storage_extension_result(
    before: Seq<u8>, bytes: Seq<u8>, after: Seq<u8>, result: Result<(), DecodeError>,
) -> bool {
    match result {
        Ok(()) => after == before + bytes,
        Err(error) => error == DecodeError::AllocationFailed && after == before,
    }
}

}
