//! Ordered conditional tile quantization creation and its normal projection.

use super::*;

verus! {

pub(crate) type Part1TileQuantizationInput = ((u16, Seq<Part1ParsedCodingStyle>), Part2Quantization);
pub(crate) type Part1TileComponentConfiguration =
    ((u16, Seq<Part1ParsedCodingStyle>), Part2Quantization, (u16, Seq<Part2Quantization>));

#[verifier::opaque]
pub(crate) open spec fn part1_prepare_tile_quantization(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc_segments: Seq<Option<Part1CodestreamSegment>>, qcd_segment: Option<Part1CodestreamSegment>,
    default_quantization: Part2Quantization, inherited_styles: (u16, Seq<Part1ParsedCodingStyle>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
) -> Result<Part1TileQuantizationInput, crate::DecodeError> {
    let initial = if cod_seen { part1_component_styles_new(components, coding_style) } else { Ok(inherited_styles) };
    match initial {
        Err(error) => Err(error),
        Ok(styles) => {
            let overrides = part1_style_overrides_from(components, coding_style, coc_segments, limits, styles, 0);
            match overrides.0 {
                Err(error) => Err(error),
                Ok(()) => {
                    let resolved = part1_resolve_decompositions(overrides.1, extensions);
                    match resolved.0 {
                        Err(error) => Err(error),
                        Ok(()) => match qcd_segment {
                            None => Ok((resolved.1, default_quantization)),
                            Some(segment) => match part1_parse_qcd_payload(segment.offset, segment.payload, coding_style) {
                                Err(error) => Err(error), Ok(value) => Ok((resolved.1, value)),
                            },
                        },
                    }
                },
            }
        },
    }
}

pub(crate) open spec fn part1_tile_quantization_finish(
    components: u16, prepared: Part1TileQuantizationInput, qcd: Option<Part1CodestreamSegment>,
    qcc: Seq<Option<Part1CodestreamSegment>>, inherited: (u16, Seq<Part2Quantization>),
) -> Result<Part1TileComponentConfiguration, crate::DecodeError> {
    let initial = if qcd.is_some() {
        part1_component_quantizations_new(components, prepared.1)
    } else { Ok(inherited) };
    match initial {
        Err(error) => Err(error),
        Ok(owner) => {
            let applied = part1_quantization_overrides_from(components, prepared.0, qcc, owner, 0);
            match applied.0 {
                Err(error) => Err(error),
                Ok(()) => Ok((prepared.0, prepared.1, applied.1)),
            }
        },
    }
}

pub(crate) open spec fn part1_tile_components_cold_run(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
) -> Option<(Result<Part1TileComponentConfiguration, crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_prepare_tile_quantization(
        components, coding_style, cod_seen, coc, qcd, default, inherited_styles, extensions, limits) {
        Err(error) => Some((Err(error), events)),
        Ok(prepared) => if qcd.is_none() || components == 0 || components > 64 {
            Some((part1_tile_quantization_finish(components, prepared, qcd, qcc, inherited), events))
        } else {
            match part1_quantization_storage_request(9, components as usize, events) {
                None => None,
                Some((Err(error), rest)) => Some((Err(error), rest)),
                Some((Ok(()), rest)) => Some((
                    part1_tile_quantization_finish(components, prepared, qcd, qcc, inherited), rest)),
            }
        },
    }
}

pub(crate) open spec fn part1_tile_components_cold_result(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
    result: Result<Part1TileComponentConfiguration, crate::DecodeError>,
) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_tile_components_cold_run(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events) == Some((result, Seq::empty()))
}

pub(crate) proof fn part1_tile_quantization_normal(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
)
    ensures match part1_prepare_tile_quantization(
        components, coding_style, cod_seen, coc, qcd, default, inherited_styles, extensions, limits) {
        Err(error) => Err(error),
        Ok(prepared) => part1_tile_quantization_finish(components, prepared, qcd, qcc, inherited),
    } == part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits),
{
    reveal(part1_prepare_tile_quantization);
    reveal(part1_finish_tile_components);
}

pub(crate) open spec fn part1_tile_components_normal_calls(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, inherited_styles: (u16, Seq<Part1ParsedCodingStyle>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
) -> Seq<Part1ColdStorageEvent> {
    let prepared = part1_prepare_tile_quantization(
        components, coding_style, cod_seen, coc, qcd, default, inherited_styles, extensions, limits);
    if prepared.is_ok() && qcd.is_some() && 0 < components <= 64 {
        seq![Part1ColdStorageEvent { site: 9, elements: components as usize, succeeded: true }]
    } else { Seq::empty() }
}

pub(crate) proof fn part1_tile_components_cold_normal(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
)
    ensures part1_tile_components_cold_result(
        components, coding_style, cod_seen, coc, qcd, default, qcc, inherited_styles, inherited, extensions, limits,
        part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
            inherited_styles, inherited, extensions, limits)),
        forall|tail: Seq<Part1ColdStorageEvent>|
            part1_tile_components_cold_run(components, coding_style, cod_seen, coc, qcd, default, qcc,
                inherited_styles, inherited, extensions, limits,
                part1_tile_components_normal_calls(components, coding_style, cod_seen, coc, qcd,
                    default, inherited_styles, extensions, limits) + tail)
                == Some((part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
                    inherited_styles, inherited, extensions, limits), tail)),
{
    part1_tile_quantization_normal(components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits);
    let prepared = part1_prepare_tile_quantization(
        components, coding_style, cod_seen, coc, qcd, default, inherited_styles, extensions, limits);
    let events = if prepared.is_ok() && qcd.is_some() && 0 < components <= 64 {
        seq![Part1ColdStorageEvent { site: 9, elements: components as usize, succeeded: true }]
    } else { Seq::empty() };
    if events.len() > 0 {
        assert(events.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty());
    }
    assert(part1_tile_components_cold_run(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events)
            == Some((part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd,
                default, qcc, inherited_styles, inherited, extensions, limits), Seq::empty())));
    assert forall|tail: Seq<Part1ColdStorageEvent>|
        part1_tile_components_cold_run(components, coding_style, cod_seen, coc, qcd, default, qcc,
            inherited_styles, inherited, extensions, limits,
            part1_tile_components_normal_calls(components, coding_style, cod_seen, coc, qcd,
                default, inherited_styles, extensions, limits) + tail)
            == Some((part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
                inherited_styles, inherited, extensions, limits), tail)) by {
        part1_tile_components_cold_frame(components, coding_style, cod_seen, coc, qcd, default, qcc,
            inherited_styles, inherited, extensions, limits, events, tail,
            part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
                inherited_styles, inherited, extensions, limits), Seq::empty());
        assert(Seq::<Part1ColdStorageEvent>::empty() + tail =~= tail);
    }
}

pub(crate) proof fn part1_tile_components_cold_refused(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits, prepared: Part1TileQuantizationInput,
    error: crate::DecodeError,
)
    requires part1_prepare_tile_quantization(
        components, coding_style, cod_seen, coc, qcd, default, inherited_styles, extensions, limits) == Ok(prepared),
        qcd.is_some(), 0 < components <= 64,
        error == crate::DecodeError::AllocationFailed,
    ensures part1_tile_components_cold_result(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, Err(error)),
{
    let response = Part1ColdStorageEvent { site: 9, elements: components as usize, succeeded: false };
    let events = seq![response];
    assert(events.drop_first() =~= Seq::<Part1ColdStorageEvent>::empty());
    assert(part1_tile_components_cold_run(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events) == Some((Err(error), Seq::empty())));
}

pub(crate) proof fn part1_tile_components_cold_frame(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits,
    events: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>,
    result: Result<Part1TileComponentConfiguration, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_components_cold_run(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events) == Some((result, rest)),
    ensures part1_tile_components_cold_run(
        components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events + tail) == Some((result, rest + tail)),
{
    if events.len() > 0 {
        assert((events + tail).drop_first() =~= events.drop_first() + tail);
    }
}

pub(crate) proof fn part1_tile_components_cold_projection(
    components: u16, coding_style: Part1ParsedCodingStyle, cod_seen: bool,
    coc: Seq<Option<Part1CodestreamSegment>>, qcd: Option<Part1CodestreamSegment>,
    default: Part2Quantization, qcc: Seq<Option<Part1CodestreamSegment>>,
    inherited_styles: (u16, Seq<Part1ParsedCodingStyle>), inherited: (u16, Seq<Part2Quantization>),
    extensions: Part2OwnedExtensions, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<Part1TileComponentConfiguration, crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>,
)
    requires part1_tile_components_cold_run(components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_finish_tile_components(components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits),
{
    part1_tile_quantization_normal(components, coding_style, cod_seen, coc, qcd, default, qcc,
        inherited_styles, inherited, extensions, limits);
}

}
