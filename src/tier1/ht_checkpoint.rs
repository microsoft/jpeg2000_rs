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
    words: Vec<u64>,
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ((result >> 16) & 0xffff) == width as u64, (result & 0xffff) == height as u64,
))]
fn geometry_word(width: u16, height: u16) -> u64 {
    let word = (u64::from(width) << 16) | u64::from(height);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(((word >> 16) & 0xffff)==width as u64 && (word & 0xffff)==height as u64) by(bit_vector)
            requires word == ((width as u64) << 16) | (height as u64);
    }
    word
}

impl PackedCleanup {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.0 == self.view().width, result.1 == self.view().height,
            result.2@ == self.cells(),
            self.view().coefficients == result.2@.map_values(|word:u64|crate::specs::compact_coefficient(word)),
    ))]
    fn header_and_cells(&self) -> (u16, u16, &[u64]) {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(PackedCleanup::view); reveal(PackedCleanup::cells); }
        // A headerless buffer denotes the raw 0×0 empty checkpoint, not
        // absence. The retained-checkpoint producer always writes a header.
        if self.words.is_empty() {
            return (0, 0, &[]);
        }
        let header = self.words[0];
        let width_bits = (header >> 16) & 0xffff;
        let height_bits = header & 0xffff;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(width_bits <= u16::MAX && height_bits <= u16::MAX) by(bit_vector)
                requires width_bits == (header >> 16) & 0xffff, height_bits == header & 0xffff;
            assert(self.view().width == width_bits as u16);
            assert(self.view().height == height_bits as u16);
        }
        (width_bits as u16, height_bits as u16, &self.words[1..])
    }
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
        closed spec fn cells(&self)->Seq<u64> {
            if self.words@.len()==0 { Seq::empty() } else { self.words@.drop_first() }
        }
        closed spec fn view(&self)->crate::specs::Tier1RawPlane {
            if self.words@.len()==0 {
                crate::specs::compact_plane(0,0,Seq::empty())
            }else{
                let header=self.words@[0];
                crate::specs::compact_plane(((header>>16) & 0xffff) as usize,(header & 0xffff) as usize,self.cells())
            }
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
    proof! { reveal(HtCleanupCheckpoint::view); reveal(PackedCleanup::view); reveal(PackedCleanup::cells); reveal(code_block_plane_view); }
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
    let elements = count + 1;
    let reserved = crate::allocation::empty_with_capacity(elements);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_ht_checkpoint_packed(code_block_plane_view(source),elements,
            match reserved { Ok(_) => Ok(()),Err(error)=>Err(error) });
    }
    let mut words = reserved?;
    let header = geometry_word(source.width, source.height);
    words.push(header);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=count,count==source.coefficients.len(),words.len()==index+1,words@[0]==header,
            crate::specs::compact_packable_plane(code_block_plane_view(source)),
            forall|i:int|0<=i<index ==> #[trigger] crate::specs::compact_coefficient(words@[i+1])
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
    let plane = PackedCleanup { words };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |i:int| 0<=i<count implies
            #[trigger] plane.view().coefficients[i]==code_block_plane_view(source).coefficients[i] by {
            assert(plane.cells()[i]==plane.words@[i+1]);
        }
        assert(plane.view().coefficients =~= code_block_plane_view(source).coefficients);
    }
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
        let (width, height, cells) = self.header_and_cells();
        let output = code_block_plane_from_dimensions(width, height, role);
        #[cfg(verus_keep_ghost)]
        proof! { if let Err(error)=output { crate::specs::part2_plane_duplicate_error(self.view(),role,error); } }
        let mut output = output?;
        if output.coefficients.len() != cells.len() {
            return Err(invalid_code_block());
        }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index<=cells.len(),
            output.width==self.view().width,output.height==self.view().height,
            output.coefficients.len()==cells.len(),
            self.view().coefficients==cells@.map_values(|word:u64|crate::specs::compact_coefficient(word)),
            crate::specs::part1_plane_duplicate_storage_result(self.view(),role,crate::specs::tier1_duplicate_plane(self.view())),
            forall|i:int|0<=i<index ==> #[trigger] coefficient_raw_view(output.coefficients@[i])==self.view().coefficients[i],
            decreases cells.len()-index,
        ))]
        while index < cells.len() {
            output.coefficients[index] = unpack_word(cells[index]);
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
        let (width, height, cells) = self.header_and_cells();
        let count = cells.len();
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
            invariant index<=count,count==cells.len(),coefficients.len()==index,
            self.view().coefficients==cells@.map_values(|word:u64|crate::specs::compact_coefficient(word)),
            forall|i:int|0<=i<index ==> #[trigger] coefficient_raw_view(coefficients@[i])==self.view().coefficients[i],
            decreases count-index,
        ))]
        while index < count {
            #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
            crate::deadline::checkpoint_periodic(index)?;
            coefficients.push(unpack_word(cells[index]));
            index += 1;
        }
        let output = CodeBlockPlane {
            width,
            height,
            coefficients,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(code_block_plane_view(&output).coefficients =~= self.view().coefficients); }
        Ok(output)
    }
}

#[cfg(test)]
mod layout_gate {
    use super::*;
    use crate::tier1::Tier1CodeBlockDecoder;

    #[test]
    fn checkpoint_header_snapshot_keeps_full_raw_dimensions_and_payload() {
        eprintln!(
            "decoder={} checkpoint={} optional={} wide={} packed={}",
            size_of::<Tier1CodeBlockDecoder>(),
            size_of::<HtCleanupCheckpoint>(),
            size_of::<Option<HtCleanupCheckpoint>>(),
            size_of::<CodeBlockPlane>(),
            size_of::<PackedCleanup>(),
        );
        let role = HtRefinementCopyRole::PacketStaging;
        let empty = PackedCleanup { words: Vec::new() };
        let zero = empty.materialize_snapshot(role).unwrap();
        assert_eq!(
            (zero.width, zero.height, zero.coefficients.len()),
            (0, 0, 0)
        );
        let raw = PackedCleanup {
            words: vec![geometry_word(u16::MAX, 0)],
        };
        let snapshot =
            crate::allocation::with_refusal(0, || raw.materialize_snapshot(role)).unwrap();
        assert_eq!(
            (snapshot.width, snapshot.height, snapshot.coefficients.len()),
            (u16::MAX, 0, 0)
        );
        let nonempty = CodeBlockPlane::new(2, 1).unwrap();
        let packed = retain_ht_cleanup(&nonempty, true).unwrap();
        assert!(matches!(packed, HtCleanupCheckpoint::Packed(_)));
        assert_eq!(packed.try_duplicate_for_storage(role).unwrap(), nonempty);
        assert_eq!(
            packed
                .read()
                .duplicate(CoefficientStorageRole::RefinementOutput)
                .unwrap(),
            nonempty
        );
    }
}
