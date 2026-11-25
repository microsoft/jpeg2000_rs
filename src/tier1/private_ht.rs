use super::ht_checkpoint::{HtCleanupCheckpoint, private_initial, private_retain};
use super::state::{arithmetic_overflow, invalid_code_block};
use super::{SubbandOrientation, Tier1BlockCoding, Tier1CodeBlockDecoder, Tier1CodingStyle};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct PrivateHtDecoder {
    primary: HtCleanupCheckpoint,
    style: Tier1CodingStyle,
    maximum_passes: u32,
    next_pass: u32,
    bitplane: u16,
    zero_bitplanes: Option<u16>,
    decoded_segments: u32,
    decoded_bytes: u64,
    cleanup: Option<HtCleanupCheckpoint>,
    refinement: Vec<u8>,
    refinement_passes: u8,
    decoded_bitplanes: u16,
    current_set: bool,
    sets_seen: u16,
    allow_sets: bool,
    magnitude_bound: u8,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl PrivateHtDecoder {
        pub(crate) closed spec fn view(&self)->crate::specs::Tier1DecoderState {
            crate::specs::Tier1DecoderState {
                plane:self.primary.view(),private_plan:true,orientation:SubbandOrientation::Ll,
                style:self.style,maximum_passes:self.maximum_passes,next_pass:self.next_pass,
                bitplane:self.bitplane,zero_bitplanes:self.zero_bitplanes,
                bitplane_state:None,mq_context_state:None,reset_contexts_before_mq:false,
                decoded_segments:self.decoded_segments,decoded_bytes:self.decoded_bytes,
                legacy_segment:None,legacy_decode_work:0,
                ht_cleanup_plane:match self.cleanup{None=>None,Some(plane)=>Some(plane.view())},
                ht_refinement_data:self.refinement@,ht_refinement_passes:self.refinement_passes,
                ht_decoded_bitplanes:self.decoded_bitplanes,ht_current_set_has_cleanup:self.current_set,
                ht_sets_seen:self.sets_seen,allow_multiple_ht_sets:self.allow_sets,
                ht_magnitude_bound:self.magnitude_bound,
            }
        }
        pub(crate) closed spec fn storage_view(&self)->crate::specs::PrivateHtDecoderState {
            crate::specs::PrivateHtDecoderState {logical:self.view(),packed:self.primary.private_is_packed()}
        }
        pub(crate) closed spec fn invariant(&self)->bool {
            crate::specs::private_ht_state_wf(self.storage_view())
        }
        pub(crate) proof fn known_fields(&self)
            ensures self.storage_view().logical==self.view(),
                self.invariant()==crate::specs::private_ht_state_wf(self.storage_view()),
        {
            reveal(PrivateHtDecoder::storage_view);reveal(PrivateHtDecoder::invariant);
        }
    }
    pub(crate) open spec fn private_decoder_outcome(result:Result<PrivateHtDecoder,DecodeError>)
        ->Result<crate::specs::PrivateHtDecoderState,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok(value.storage_view())}
    }
    spec fn private_prepare_outcome(result:Result<crate::transform::SignedMagnitude,DecodeError>)
        ->Result<crate::specs::Part1QuantizedCoefficient,DecodeError> {
        match result{Err(error)=>Err(error),Ok(value)=>Ok((crate::magnitude::magnitude_limbs(value.magnitude),value.negative))}
    }
}

#[cfg(test)]
#[allow(
    clippy::items_after_test_module,
    reason = "Keep private storage regressions adjacent to the owner definition."
)]
mod tests {
    use super::*;
    use crate::tier1::{CodeBlockPlane, CoefficientState};

    fn configured(width: u16, height: u16) -> PrivateHtDecoder {
        let mut style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        style.set_force_high_throughput(true);
        new_private_ht_decoder(width, height, 2, style, true, 74).unwrap()
    }

    #[test]
    fn private_primary_release_layout_and_real_initial_owner() {
        eprintln!(
            "legacy={} private={} coefficient={} packed-owner={} optional-checkpoint={}",
            size_of::<Tier1CodeBlockDecoder>(),
            size_of::<PrivateHtDecoder>(),
            size_of::<CoefficientState>(),
            size_of::<HtCleanupCheckpoint>(),
            size_of::<Option<HtCleanupCheckpoint>>(),
        );
        assert_eq!(size_of::<Tier1CodeBlockDecoder>(), 432);
        assert_eq!(size_of::<CoefficientState>(), 56);
        let decoder = configured(2, 1);
        assert!(matches!(decoder.primary, HtCleanupCheckpoint::Packed(_)));
        assert_eq!(decoder.dimensions(), (2, 1));
        assert_eq!(decoder.collect().unwrap().len(), 2);
    }

    #[test]
    fn private_primary_replays_actual_spp_mrp_and_replacement() {
        let limits = ResourceLimits::default();
        let mut decoder = configured(1, 1);
        let mut reference = configured(1, 1).into_wide().unwrap();
        for cleanup in [true, false, false, true] {
            let mut wide = decoder.stage().unwrap().into_wide().unwrap();
            let execute = |state: &mut Tier1CodeBlockDecoder| {
                if cleanup {
                    state.decode_high_throughput_segments(&[0, 0x63, 0], 1, None, 0, &limits)
                } else {
                    state.decode_high_throughput_refinement(&[0], 1, &limits)
                }
            };
            assert_eq!(execute(&mut wide), execute(&mut reference));
            decoder = from_wide(wide).unwrap();
            assert!(matches!(decoder.primary, HtCleanupCheckpoint::Packed(_)));
            let actual = decoder.stage().unwrap().into_wide().unwrap();
            assert_eq!(actual.plane(), reference.plane());
            assert_eq!(actual.next_pass(), reference.next_pass());
            assert_eq!(actual.decoded_bytes(), reference.decoded_bytes());
        }
    }

    #[test]
    fn private_primary_preserves_all_raw_fields_and_lossless_wide_fallback() {
        let mut source = configured(2, 1).into_wide().unwrap();
        source.plane.coefficients[0] = CoefficientState {
            magnitude: u64::from(u32::MAX),
            magnitude_high: [0; 5],
            legacy_bitplane: Some(62),
            significant: true,
            negative: true,
            refined: true,
        };
        let expected = source.plane.clone();
        let packed = from_wide(source).unwrap();
        assert!(matches!(packed.primary, HtCleanupCheckpoint::Packed(_)));
        assert_eq!(
            packed.stage().unwrap().into_wide().unwrap().plane(),
            &expected
        );
        for coefficient in [
            CoefficientState {
                magnitude: u64::from(u32::MAX) + 1,
                ..expected.coefficients[0]
            },
            CoefficientState {
                magnitude_high: [1, 2, 3, 4, 5],
                ..expected.coefficients[0]
            },
            CoefficientState {
                legacy_bitplane: Some(63),
                ..expected.coefficients[0]
            },
        ] {
            let mut source = configured(2, 1).into_wide().unwrap();
            source.plane.coefficients[0] = coefficient;
            let expected = source.plane.clone();
            let wide = from_wide(source).unwrap();
            assert!(matches!(wide.primary, HtCleanupCheckpoint::Wide(_)));
            assert_eq!(
                wide.stage().unwrap().into_wide().unwrap().plane(),
                &expected
            );
        }
        let mut malformed = configured(2, 1).into_wide().unwrap();
        malformed.plane.width = 0;
        malformed.plane.height = u16::MAX;
        malformed.plane.coefficients.clear();
        let retained = from_wide(malformed).unwrap();
        assert!(matches!(retained.primary, HtCleanupCheckpoint::Wide(_)));
        assert_eq!(retained.dimensions(), (0, u16::MAX));
        assert!(retained.collect().unwrap().is_empty());
    }

    #[test]
    fn private_primary_actual_coded_bitplanes_promote_and_late_refusals_roll_back() {
        let limits = ResourceLimits::default();
        let mut style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
        style.set_force_high_throughput(true);
        let create = || new_private_ht_decoder(1, 1, 40, style, true, 74).unwrap();
        let mut state = crate::packet::CodeBlockPacketState::new();
        let mut inclusion = crate::packet::TagTree::new(1, 1, &limits).unwrap();
        let mut zero = crate::packet::TagTree::new(1, 1, &limits).unwrap();
        let mut reader = crate::packet::PacketBitReader::new(&[0xe3], &limits).unwrap();
        assert!(reader.read_bit().unwrap());
        let contribution = crate::packet::decode_code_block_contribution(
            &mut state,
            &mut inclusion,
            &mut zero,
            crate::packet::CodeBlockPacketContext {
                leaf_x: 0,
                leaf_y: 0,
                layer: 0,
                maximum_zero_bitplanes: 40,
                tier1_style: style,
            },
            &mut reader,
        )
        .unwrap()
        .unwrap();
        assert_eq!(contribution.data_length, 3);
        let mut reference = create().into_wide().unwrap();
        let expected =
            crate::packet::private_ht_body(&mut reference, &contribution, &[0, 0x63, 0], &limits)
                .unwrap();
        let mut success = false;
        let mut first_refusal = false;
        let mut later_refusal = false;
        for after in 0..24 {
            let mut actual = create();
            let before = format!("{actual:?}");
            match crate::allocation::with_refusal(after, || {
                actual.decode(&contribution, &[0, 0x63, 0], &limits)
            }) {
                Err(DecodeError::AllocationFailed) => {
                    first_refusal |= after == 0;
                    later_refusal |= after > 0;
                    assert_eq!(format!("{actual:?}"), before);
                }
                Ok(decoded) => {
                    success = true;
                    assert_eq!(decoded, expected);
                    assert!(matches!(actual.primary, HtCleanupCheckpoint::Wide(_)));
                    assert_eq!(
                        actual.stage().unwrap().into_wide().unwrap().plane(),
                        reference.plane()
                    );
                }
                Err(error) => panic!("unexpected promotion result: {error:?}"),
            }
        }
        assert!(success && first_refusal && later_refusal);
    }

    #[test]
    fn private_primary_refusal_and_independent_geometry_are_explicit() {
        let source = configured(2, 1);
        assert!(matches!(
            crate::allocation::with_refusal(0, || source.stage()),
            Err(DecodeError::AllocationFailed)
        ));
        let staged = source.stage().unwrap();
        assert!(matches!(
            crate::allocation::with_refusal(0, || staged.into_wide()),
            Err(DecodeError::AllocationFailed)
        ));
        assert_eq!(source.dimensions(), (2, 1));
        let mut wide = source.into_wide().unwrap();
        wide.plane.coefficients[0].magnitude = 3;
        wide.plane.coefficients[0].significant = true;
        wide.ht_cleanup_plane = Some(private_retain(wide.plane.clone()).unwrap());
        wide.plane = CodeBlockPlane::new(1, 1).unwrap();
        wide.ht_current_set_has_cleanup = true;
        wide.ht_decoded_bitplanes = 2;
        wide.next_pass = 1;
        let private = from_wide(wide).unwrap();
        assert_eq!(private.dimensions(), (1, 1));
        let mut restored = private.stage().unwrap().into_wide().unwrap();
        for _ in 0..2 {
            restored
                .decode_high_throughput_refinement(&[1], 1, &ResourceLimits::default())
                .unwrap();
        }
        let retained = from_wide(restored).unwrap();
        assert_eq!(retained.dimensions(), (2, 1));
        assert!(matches!(retained.primary, HtCleanupCheckpoint::Packed(_)));
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::private_ht_initial_result(crate::specs::PrivateHtInitialContext {
            width,height,bitplanes,style,allowed:allow_sets,bound:magnitude_bound,
        },private_decoder_outcome(result)),
        private_decoder_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
            private_decoder_outcome(result)==crate::specs::private_ht_initial_value(crate::specs::PrivateHtInitialContext {
                width,height,bitplanes,style,allowed:allow_sets,bound:magnitude_bound,
            }),
        match result{Ok(value)=>value.invariant(),Err(_)=>true},
))]
pub(crate) fn new_private_ht_decoder(
    width: u16,
    height: u16,
    bitplanes: u16,
    style: Tier1CodingStyle,
    allow_sets: bool,
    magnitude_bound: u8,
) -> Result<PrivateHtDecoder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost ctx=crate::specs::PrivateHtInitialContext {
        width,height,bitplanes,style,allowed:allow_sets,bound:magnitude_bound,
    };}
    if !matches!(style.block_coding, Tier1BlockCoding::HighThroughput)
        || !style.force_high_throughput
        || bitplanes == 0
        || bitplanes > super::MAX_TIER1_BITPLANES
        || magnitude_bound == 0
        || magnitude_bound > super::MAX_HT_MAGNITUDE_BITS
    {
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_tier1_storage_pure::<crate::specs::PrivateHtDecoderState>(Err(
                crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)));
        }
        return Err(invalid_code_block());
    }
    let initialized = private_initial(width, height);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_ht_initial_observed(ctx,super::ht_checkpoint::private_primary_outcome(initialized));}
    let primary = initialized?;
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtDecoder::view);reveal(PrivateHtDecoder::storage_view);reveal(PrivateHtDecoder::invariant);
    }
    Ok(PrivateHtDecoder {
        primary,
        style,
        maximum_passes: u32::from(bitplanes) * 3 - 2,
        next_pass: 0,
        bitplane: bitplanes - 1,
        zero_bitplanes: None,
        decoded_segments: 0,
        decoded_bytes: 0,
        cleanup: None,
        refinement: Vec::new(),
        refinement_passes: 0,
        decoded_bitplanes: 0,
        current_set: false,
        sets_seen: 0,
        allow_sets,
        magnitude_bound,
    })
}

impl PrivateHtDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),
        ensures match result{Ok(value)=>value.view()==self.view(),Err(error)=>error==DecodeError::AllocationFailed},
            crate::specs::private_ht_stage_result(self.storage_view(),private_decoder_outcome(result)),
            match result{Ok(value)=>value.invariant() && value.storage_view()==self.storage_view(),Err(_)=>true},
    ))]
    fn stage(&self) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtDecoder::view);reveal(PrivateHtDecoder::storage_view);reveal(PrivateHtDecoder::invariant);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=self.storage_view();}
        let copied_primary = self.primary.private_copy();
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=copied_primary{crate::specs::private_ht_stage_primary_error(before,error);}}
        let primary = copied_primary?;
        let cleanup = match &self.cleanup {
            None => {
                #[cfg(verus_keep_ghost)]
                proof! {crate::specs::part2_decoder_cleanup_none(super::HtRefinementCopyRole::PacketStaging);}
                None
            }
            Some(source) => {
                let copied =
                    source.try_duplicate_for_storage(super::HtRefinementCopyRole::PacketStaging);
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::specs::part2_decoder_cleanup_observed(source.view(),
                        super::HtRefinementCopyRole::PacketStaging,super::code_block_plane_outcome(copied));
                    if let Err(error)=copied {crate::specs::private_ht_stage_cleanup_error(before,error);}
                }
                let copied = copied?;
                #[cfg(verus_keep_ghost)]
                proof! {super::ht_checkpoint::checkpoint_wide_view(copied);}
                Some(HtCleanupCheckpoint::Wide(copied))
            }
        };
        let copied_bytes = super::ht_refinement::copy_ht_refinement_bytes(
            &self.refinement,
            super::HtRefinementCopyRole::PacketStaging,
        );
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_ht_stage_bytes_observed(before,super::ht_byte_vector_outcome(copied_bytes));}
        let refinement = copied_bytes?;
        Ok(Self {
            primary,
            style: self.style,
            maximum_passes: self.maximum_passes,
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            zero_bitplanes: self.zero_bitplanes,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            cleanup,
            refinement,
            refinement_passes: self.refinement_passes,
            decoded_bitplanes: self.decoded_bitplanes,
            current_set: self.current_set,
            sets_seen: self.sets_seen,
            allow_sets: self.allow_sets,
            magnitude_bound: self.magnitude_bound,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),
        ensures match result{Ok(value)=>super::tier1_decoder_state(&value)==self.view(),Err(_)=>true},
            crate::specs::private_ht_into_wide_result(self.storage_view(),super::tier1_initial_decoder_outcome(result)),
            match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(_)=>true},
    ))]
    fn into_wide(self) -> Result<Tier1CodeBlockDecoder, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(PrivateHtDecoder::view);reveal(PrivateHtDecoder::storage_view);reveal(PrivateHtDecoder::invariant);
            reveal(super::tier1_decoder_state);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost before=self.storage_view();}
        let converted = self.primary.private_materialize();
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_ht_into_wide_observed(before,super::code_block_plane_outcome(converted));}
        let plane = converted?;
        Ok(Tier1CodeBlockDecoder {
            plane,
            private_plan: true,
            orientation: SubbandOrientation::Ll,
            style: self.style,
            maximum_passes: self.maximum_passes,
            next_pass: self.next_pass,
            bitplane: self.bitplane,
            zero_bitplanes: self.zero_bitplanes,
            bitplane_state: None,
            mq_context_state: None,
            reset_contexts_before_mq: false,
            decoded_segments: self.decoded_segments,
            decoded_bytes: self.decoded_bytes,
            legacy_segment: None,
            legacy_decode_work: 0,
            ht_cleanup_plane: self.cleanup,
            ht_refinement_data: self.refinement,
            ht_refinement_passes: self.refinement_passes,
            ht_decoded_bitplanes: self.decoded_bitplanes,
            ht_current_set_has_cleanup: self.current_set,
            ht_sets_seen: self.sets_seen,
            allow_multiple_ht_sets: self.allow_sets,
            ht_magnitude_bound: self.magnitude_bound,
        })
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match result{Ok(value)=>value.view()==super::tier1_decoder_state(&wide),Err(_)=>true},
            crate::specs::private_ht_from_wide_result(super::tier1_decoder_state(&wide),private_decoder_outcome(result)),
            match result{Ok(value)=>value.invariant()
                && value.storage_view().packed==crate::specs::private_primary_selected(super::tier1_decoder_state(&wide).plane),Err(_)=>true},
            crate::specs::private_ht_metadata_supported(super::tier1_decoder_state(&wide)) ==>
                match result{Err(error)=>error==DecodeError::AllocationFailed,Ok(_)=>true},
    ))]
fn from_wide(wide: Tier1CodeBlockDecoder) -> Result<PrivateHtDecoder, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(PrivateHtDecoder::view);reveal(PrivateHtDecoder::storage_view);reveal(PrivateHtDecoder::invariant);
        reveal(super::tier1_decoder_state);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {let ghost before=super::tier1_decoder_state(&wide);}
    if wide.bitplane_state.is_some()
        || wide.mq_context_state.is_some()
        || wide.legacy_segment.is_some()
        || wide.reset_contexts_before_mq
        || wide.legacy_decode_work != 0
        || !wide.private_plan
        || !wide.style.force_high_throughput
        || !matches!(wide.orientation, SubbandOrientation::Ll)
        || !matches!(wide.style.block_coding, Tier1BlockCoding::HighThroughput)
    {
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::part2_tier1_storage_pure::<crate::specs::PrivateHtDecoderState>(Err(
        crate::specs::ht_reader_error(crate::MalformedKind::InvalidCodeBlock)));}
        return Err(invalid_code_block());
    }
    let retained = private_retain(wide.plane);
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::private_ht_from_wide_observed(before,super::ht_checkpoint::private_primary_outcome(retained));}
    let primary = retained?;
    Ok(PrivateHtDecoder {
        primary,
        style: wide.style,
        maximum_passes: wide.maximum_passes,
        next_pass: wide.next_pass,
        bitplane: wide.bitplane,
        zero_bitplanes: wide.zero_bitplanes,
        decoded_segments: wide.decoded_segments,
        decoded_bytes: wide.decoded_bytes,
        cleanup: wide.ht_cleanup_plane,
        refinement: wide.ht_refinement_data,
        refinement_passes: wide.ht_refinement_passes,
        decoded_bitplanes: wide.ht_decoded_bitplanes,
        current_set: wide.ht_current_set_has_cleanup,
        sets_seen: wide.ht_sets_seen,
        allow_sets: wide.allow_multiple_ht_sets,
        magnitude_bound: wide.ht_magnitude_bound,
    })
}

impl PrivateHtDecoder {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.invariant(),
        ensures final(self).invariant(),
            crate::specs::private_ht_body_result(old(self).storage_view(),crate::packet::code_block_contribution_view(contribution),body@,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits),(result,final(self).storage_view())),
            result.is_err() ==> final(self).storage_view()==old(self).storage_view(),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).storage_view())==
                crate::specs::private_ht_body_value(old(self).storage_view(),crate::packet::code_block_contribution_view(contribution),body@,
                    crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                    crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
            result!=Err(DecodeError::AllocationFailed) ==> (result,final(self).view())==crate::specs::part1_code_block_body_transaction(
                old(self).view(),crate::packet::code_block_contribution_view(contribution),body@,
                crate::limits::resource_code_block_pass_limit(limits),crate::limits::resource_code_block_byte_limit(limits),
                crate::limits::resource_input_byte_limit(limits),crate::limits::resource_work_limit(limits)),
    ))]
    pub(crate) fn decode(
        &mut self,
        contribution: &crate::packet::CodeBlockContribution,
        body: &[u8],
        limits: &ResourceLimits,
    ) -> Result<crate::packet::CodeBlockBodyDecode, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost ctx=crate::specs::PrivateHtBodyContext {
            before:self.storage_view(),header:crate::packet::code_block_contribution_view(contribution),body:body@,
            passes:crate::limits::resource_code_block_pass_limit(limits),bytes:crate::limits::resource_code_block_byte_limit(limits),
            input:crate::limits::resource_input_byte_limit(limits),work:crate::limits::resource_work_limit(limits),
        };}
        #[cfg(verus_keep_ghost)]
        proof! {
            self.known_fields();
            crate::specs::private_ht_body_value_fields(ctx.before,ctx.header,ctx.body,ctx.passes,ctx.bytes,ctx.input,ctx.work);
        }
        let copied = self.stage();
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=copied{crate::specs::private_ht_body_stage_error(ctx,error);}}
        let staged = copied?;
        let converted = staged.into_wide();
        #[cfg(verus_keep_ghost)]
        proof! {if let Err(error)=converted{crate::specs::private_ht_body_materialize_error(ctx,error);}}
        let mut wide = converted?;
        let decoded = crate::packet::private_ht_body(&mut wide, contribution, body, limits);
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost kernel=(decoded,super::tier1_decoder_state(&wide));}
        #[cfg(verus_keep_ghost)]
        proof! {
            if decoded.is_err(){crate::specs::private_ht_body_kernel_error(ctx,kernel);}
            else{
                crate::specs::private_ht_staged_metadata(ctx.before.logical,ctx.header,ctx.body,
                    ctx.passes,ctx.bytes,ctx.input,ctx.work);
            }
        }
        let result = decoded?;
        let retained_result = from_wide(wide);
        #[cfg(verus_keep_ghost)]
        proof! {crate::specs::private_ht_body_retained(ctx,kernel,private_decoder_outcome(retained_result));}
        let retained = retained_result?;
        *self = retained;
        Ok(result)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.0==self.view().plane.width,result.1==self.view().plane.height,
    ))]
    pub(crate) fn dimensions(&self) -> (u16, u16) {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(PrivateHtDecoder::view);}
        self.primary.private_dimensions()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures private_prepare_outcome(result)==crate::specs::part1_prepare_signed_cell(self.view().plane,x,y),
    ))]
    fn prepare_cell(
        &self,
        x: u16,
        y: u16,
    ) -> Result<crate::transform::SignedMagnitude, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(PrivateHtDecoder::view);}
        let (width, height) = self.dimensions();
        if x >= width || y >= height {
            return Err(invalid_code_block());
        }
        let row = usize::from(y)
            .checked_mul(usize::from(width))
            .ok_or_else(arithmetic_overflow)?;
        let index = row
            .checked_add(usize::from(x))
            .ok_or_else(arithmetic_overflow)?;
        self.primary.private_coefficient(index)?.signed_magnitude()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::specs::part2_coefficient_collect_result(self.view().plane,crate::transform::quantized_coefficients_outcome(result)),
            crate::transform::quantized_coefficients_outcome(result)!=Err(DecodeError::AllocationFailed) ==>
                crate::transform::quantized_coefficients_outcome(result)==crate::specs::part1_prepare_collect_coefficients(self.view().plane),
    ))]
    pub(crate) fn collect(&self) -> Result<Vec<crate::transform::SignedMagnitude>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {let ghost source=self.view().plane;}
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_extraction_normal(source,true);
            crate::specs::part2_coefficient_collect_normal(source);
        }
        let (width, height) = self.dimensions();
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(private_prepare_outcome);
            assert((width as int)*(height as int)<=usize::MAX) by(nonlinear_arith)
                requires width<=65535,height<=65535;
        }
        let count = usize::from(width)
            .checked_mul(usize::from(height))
            .ok_or_else(arithmetic_overflow)?;
        let allocated = if count == 0 {
            Ok(Vec::new())
        } else {
            crate::allocation::empty_with_capacity(count)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::specs::part2_extraction_capacity_observed(crate::specs::part2_extraction_context(source,true),
                match allocated{Ok(_)=>Ok(()),Err(error)=>Err(error)});
            if let Err(error)=allocated{
                crate::specs::part2_extraction_refused(source,true,error);
                crate::specs::part2_coefficient_collect_observed(source,Err(error));
            }
        }
        let mut output = allocated?;
        let mut y = 0u16;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::transform::representation_proofs::quantized_coefficients_fields(output@);
            crate::proofs::production_impl::production_prepare_rows_empty(source);
            assert(crate::transform::quantized_coefficients_view(output@) =~= Seq::empty());
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant y<=height,width==source.width,height==source.height,source==self.view().plane,
                count as nat==width as nat*height as nat,
                output.len() as nat==y as nat*width as nat,
                crate::specs::part2_extraction_result(source,true,crate::specs::part1_prepare_collect_coefficients(source)),
                crate::specs::part2_coefficient_collect_result(source,crate::specs::part1_prepare_collect_coefficients(source)),
                crate::specs::part1_prepare_coefficient_rows(source,y as nat)==Ok(crate::transform::quantized_coefficients_view(output@)),
            decreases height-y,
        ))]
        while y < height {
            #[cfg(verus_keep_ghost)]
            proof! {crate::transform::representation_proofs::quantized_coefficients_fields(output@);}
            #[cfg(verus_keep_ghost)]
            proof_decl! {let ghost row_start=crate::transform::quantized_coefficients_view(output@);}
            let mut x = 0u16;
            #[cfg(verus_keep_ghost)]
            proof! {crate::proofs::production_impl::production_prepare_row_empty(source,y,row_start);}
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant x<=width,y<height,width==source.width,height==source.height,source==self.view().plane,
                    count as nat==width as nat*height as nat,
                    row_start.len()==y as nat*width as nat,
                    output.len() as nat==y as nat*width as nat+x as nat,
                    crate::specs::part2_extraction_result(source,true,crate::specs::part1_prepare_collect_coefficients(source)),
                    crate::specs::part2_coefficient_collect_result(source,crate::specs::part1_prepare_collect_coefficients(source)),
                    crate::specs::part1_prepare_coefficient_rows(source,y as nat)==Ok(row_start),
                    crate::specs::part1_prepare_coefficient_row(source,y,row_start,x as nat)==Ok(crate::transform::quantized_coefficients_view(output@)),
                decreases width-x,
            ))]
            while x < width {
                #[cfg(all(feature = "cooperative-deadlines", not(verus_keep_ghost)))]
                crate::deadline::checkpoint_periodic(
                    usize::from(y) * usize::from(width) + usize::from(x),
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(private_prepare_outcome);
                    crate::proofs::production_impl::production_prepare_row_step(source,y,row_start,x as nat);
                }
                let prepared = self.prepare_cell(x, y);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(private_prepare_outcome(prepared)==crate::specs::part1_prepare_signed_cell(source,x,y));
                    if let Err(error)=prepared{
                        assert(crate::specs::part1_prepare_signed_cell(source,x,y)==Err(error));
                    }
                }
                let value = match prepared {
                    Ok(value) => value,
                    Err(error) => {
                        #[cfg(verus_keep_ghost)]
                        proof! {
                            crate::proofs::production_impl::production_prepare_row_error(source,y,row_start,x as nat+1,width as nat,error);
                            crate::proofs::production_impl::production_prepare_rows_step(source,y as nat);
                            crate::proofs::production_impl::production_prepare_rows_error(source,y as nat+1,height as nat,error);
                        }
                        return Err(error);
                    }
                };
                #[cfg(verus_keep_ghost)]
                proof_decl! {let ghost before_values=output@;}
                output.push(value);
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::transform::representation_proofs::quantized_coefficients_fields(output@);
                    crate::transform::representation_proofs::quantized_coefficients_push(before_values,value);
                }
                x = x.checked_add(1).ok_or_else(arithmetic_overflow)?;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_prepare_rows_step(source,y as nat);
                assert(y as nat*width as nat+width as nat==(y as nat+1)*width as nat) by(nonlinear_arith);
            }
            y = y.checked_add(1).ok_or_else(arithmetic_overflow)?;
        }
        Ok(output)
    }
}
