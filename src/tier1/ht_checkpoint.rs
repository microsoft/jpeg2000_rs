use super::compact_legacy::{pack_word, packable, unpack_word};
use super::state::{code_block_plane_from_dimensions, invalid_code_block};
use super::{CodeBlockPlane, CoefficientStorageRole, HtRefinementCopyRole};
#[cfg(verus_keep_ghost)]
use super::{code_block_plane_outcome, code_block_plane_view, coefficient_raw_view};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(super) struct PackedCleanup {
    width: u16,
    height: u16,
    words: Vec<u64>,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(super) enum HtCleanupCheckpoint {
    Wide(CodeBlockPlane),
    Packed(PackedCleanup),
}

pub(super) enum HtCheckpointRef<'a> {
    Wide(&'a CodeBlockPlane),
    Packed(&'a PackedCleanup),
}

#[cfg(verus_keep_ghost)]
verus! {
    impl PackedCleanup {
        closed spec fn view(&self)->crate::specs::Tier1RawPlane {
            crate::specs::compact_plane(self.width as usize,self.height as usize,self.words@)
        }
    }

    impl HtCleanupCheckpoint {
        pub closed spec fn view(&self)->crate::specs::Tier1RawPlane {
            match self { Self::Wide(plane)=>code_block_plane_view(plane), Self::Packed(plane)=>plane.view() }
        }
    }

    pub(super) proof fn checkpoint_wide_view(source:CodeBlockPlane)
        ensures HtCleanupCheckpoint::Wide(source).view()==code_block_plane_view(&source),
    {
        reveal(HtCleanupCheckpoint::view);
    }

    impl HtCheckpointRef<'_> {
        pub(super) closed spec fn view(&self)->crate::specs::Tier1RawPlane {
            match self { Self::Wide(plane)=>code_block_plane_view(*plane), Self::Packed(plane)=>plane.view() }
        }
    }

    pub(super) open spec fn checkpoint_outcome(result: Result<HtCleanupCheckpoint,DecodeError>)
        -> Result<crate::specs::Tier1RawPlane,DecodeError> {
        match result { Err(error)=>Err(error), Ok(plane)=>Ok(plane.view()) }
    }
}

impl Clone for HtCleanupCheckpoint {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.view()==self.view(),
    ))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(HtCleanupCheckpoint::view); reveal(PackedCleanup::view); }
        match self {
            Self::Wide(plane) => Self::Wide(plane.clone()),
            Self::Packed(plane) => Self::Packed(PackedCleanup {
                width: plane.width,
                height: plane.height,
                words: plane.words.clone(),
            }),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result==crate::specs::compact_packable_plane(code_block_plane_view(source)),
))]
fn cleanup_packable(source: &CodeBlockPlane) -> bool {
    let mut index = 0;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(code_block_plane_view); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index<=source.coefficients.len(),
        forall|i:int|0<=i<index ==> #[trigger]
            crate::specs::compact_packable_coefficient(code_block_plane_view(source).coefficients[i]),
        decreases source.coefficients.len()-index,
    ))]
    while index < source.coefficients.len() {
        #[cfg(verus_keep_ghost)]
        proof! { assert(code_block_plane_view(source).coefficients[index as int]==coefficient_raw_view(source.coefficients@[index as int])); }
        if !packable(source.coefficients[index]) {
            return false;
        }
        index += 1;
    }
    true
}

impl HtCleanupCheckpoint {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.view()==self.view(),
    ))]
    pub(super) fn read(&self) -> HtCheckpointRef<'_> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(HtCleanupCheckpoint::view); reveal(HtCheckpointRef::view); }
        match self {
            Self::Wide(plane) => HtCheckpointRef::Wide(plane),
            Self::Packed(plane) => HtCheckpointRef::Packed(plane),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_ht_checkpoint_result(code_block_plane_view(source),private_plan,checkpoint_outcome(result)),
            checkpoint_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                checkpoint_outcome(result)==crate::specs::tier1_duplicate_plane(code_block_plane_view(source)),
    ))]
pub(super) fn retain_ht_cleanup(
    source: &CodeBlockPlane,
    private_plan: bool,
) -> Result<HtCleanupCheckpoint, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(HtCleanupCheckpoint::view); reveal(PackedCleanup::view); reveal(code_block_plane_view); }
    let count = source.coefficients.len();
    let width = usize::from(source.width);
    let height = usize::from(source.height);
    #[cfg(verus_keep_ghost)]
    proof! { assert(width*height<=usize::MAX) by(nonlinear_arith) requires width<=65535,height<=65535; }
    if !private_plan
        || width == 0
        || height == 0
        || count == 0
        || count > 4096
        || width * height != count
        || !cleanup_packable(source)
    {
        let wide = source.duplicate(CoefficientStorageRole::CleanupCopy);
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part2_ht_checkpoint_wide(code_block_plane_view(source),private_plan,code_block_plane_outcome(wide)); }
        return Ok(HtCleanupCheckpoint::Wide(wide?));
    }
    let reserved = crate::allocation::empty_with_capacity(count);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_ht_checkpoint_packed(code_block_plane_view(source),
            match reserved { Ok(_) => Ok(()),Err(error)=>Err(error) });
    }
    let mut words = reserved?;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=count,count==source.coefficients.len(),words.len()==index,
            crate::specs::compact_packable_plane(code_block_plane_view(source)),
            forall|i:int|0<=i<index ==> #[trigger] crate::specs::compact_coefficient(words@[i])
                ==code_block_plane_view(source).coefficients[i],
            decreases count-index,
        ))]
    while index < count {
        #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
        crate::deadline::checkpoint_periodic(index)?;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::specs::compact_packable_coefficient(code_block_plane_view(source).coefficients[index as int]));
        }
        words.push(pack_word(source.coefficients[index]));
        index += 1;
    }
    let plane = PackedCleanup {
        width: source.width,
        height: source.height,
        words,
    };
    #[cfg(verus_keep_ghost)]
    proof! { assert(plane.view().coefficients =~= code_block_plane_view(source).coefficients); }
    Ok(HtCleanupCheckpoint::Packed(plane))
}

impl HtCleanupCheckpoint {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_decoder_plane_result(self.view(),role,true,code_block_plane_outcome(result)),
            match result { Ok(plane)=>code_block_plane_view(&plane)==self.view(), Err(error)=>error==DecodeError::AllocationFailed },
    ))]
    pub(super) fn try_duplicate_for_storage(
        &self,
        role: HtRefinementCopyRole,
    ) -> Result<CodeBlockPlane, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(HtCleanupCheckpoint::view); }
        match self {
            Self::Wide(plane) => plane.try_duplicate_raw(role, true, false),
            // Snapshot APIs use a real independently writable dense owner.
            Self::Packed(plane) => plane.materialize_snapshot(role),
        }
    }
}

impl HtCheckpointRef<'_> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_plane_duplicate_storage_result(self.view(),role,code_block_plane_outcome(result)),
            code_block_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                code_block_plane_outcome(result)==crate::specs::tier1_duplicate_plane(self.view()),
    ))]
    pub(super) fn duplicate(
        &self,
        role: CoefficientStorageRole,
    ) -> Result<CodeBlockPlane, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(HtCheckpointRef::view); }
        match self {
            Self::Wide(plane) => plane.duplicate(role),
            Self::Packed(plane) => plane.materialize(role),
        }
    }
}

impl PackedCleanup {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part1_plane_duplicate_storage_result(self.view(),role,code_block_plane_outcome(result)),
            code_block_plane_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                code_block_plane_outcome(result)==crate::specs::tier1_duplicate_plane(self.view()),
    ))]
    fn materialize(&self, role: CoefficientStorageRole) -> Result<CodeBlockPlane, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PackedCleanup::view);
            reveal(code_block_plane_view);
            crate::specs::part2_plane_duplicate_normal(self.view(),role);
        }
        let output = code_block_plane_from_dimensions(self.width, self.height, role);
        #[cfg(verus_keep_ghost)]
        proof! { if let Err(error)=output { crate::specs::part2_plane_duplicate_error(self.view(),role,error); } }
        let mut output = output?;
        if output.coefficients.len() != self.words.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=self.words.len(),
            output.width==self.width,output.height==self.height,
            output.coefficients.len()==self.words.len(),
            crate::specs::part1_plane_duplicate_storage_result(self.view(),role,crate::specs::tier1_duplicate_plane(self.view())),
            forall|i:int|0<=i<index ==> #[trigger] coefficient_raw_view(output.coefficients@[i])==self.view().coefficients[i],
            decreases self.words.len()-index,
        ))]
        while index < self.words.len() {
            output.coefficients[index] = unpack_word(self.words[index]);
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(code_block_plane_view(&output).coefficients =~= self.view().coefficients); }
        Ok(output)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_decoder_plane_result(self.view(),_role,true,code_block_plane_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(value)=>code_block_plane_view(&value)==self.view()},
    ))]
    fn materialize_snapshot(
        &self,
        _role: HtRefinementCopyRole,
    ) -> Result<CodeBlockPlane, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(PackedCleanup::view); reveal(code_block_plane_view); }
        let count = self.words.len();
        let reserved = if count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(count)
        };
        #[cfg(verus_keep_ghost)]
        proof! { crate::specs::part2_decoder_plane_observed(self.view(),_role,true,
        match reserved { Ok(_) => Ok(()),Err(error)=>Err(error) }); }
        let mut coefficients = reserved?;
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=count,count==self.words.len(),coefficients.len()==index,
            forall|i:int|0<=i<index ==> #[trigger] coefficient_raw_view(coefficients@[i])==self.view().coefficients[i],
            decreases count-index,
        ))]
        while index < count {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(index)?;
            coefficients.push(unpack_word(self.words[index]));
            index += 1;
        }
        let output = CodeBlockPlane {
            width: self.width,
            height: self.height,
            coefficients,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(code_block_plane_view(&output).coefficients =~= self.view().coefficients); }
        Ok(output)
    }
}
