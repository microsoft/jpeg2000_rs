//! Fresh progression-admission scratch storage at its actual validated frontier.
use super::*;
use crate::codestream::{ComponentCodingStyles, MctCopyPath, ProgressionChange};
verus! {

pub(crate) open spec fn part1_bitmap_count(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits) -> Option<usize> {
    if records.len() == 0 { None } else {
        match part1_poc_validation_shape(offset, layers, styles, 0, 0, 0) {
            Err(_) => None,
            Ok(shape) => {
                let cost = (records.len() as u64) as int * (shape.0 as u64) as int;
                if cost > u64::MAX || cost > crate::limits::resource_work_limit(limits) { None }
                else { Some(shape.0) }
            },
        }
    }
}
pub(crate) open spec fn part1_bitmap_requests(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits) -> Seq<Part1MctCopyRequest> {
    match part1_bitmap_count(offset, records, layers, styles, limits) {
        None => Seq::empty(),
        Some(count) => part1_mct_copy_leaf(MctCopyPath::ProgressionBitmap(offset, layers,
            crate::codestream::component_coding_style_count(styles), records.len() as usize), count),
    }
}
pub(crate) open spec fn part1_bitmap_run(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>)
    -> Option<(Result<(), crate::DecodeError>, Seq<Part1ColdStorageEvent>)> {
    match part1_mct_copy_run(part1_bitmap_requests(offset, records, layers, styles, limits), events) {
        None => None, Some((Err(error), rest)) => Some((Err(error), rest)),
        Some((Ok(()), rest)) => Some((part1_validate_progression_changes(offset, records, layers, styles, limits), rest)),
    }
}
#[verifier::opaque]
pub(crate) open spec fn part1_bitmap_result(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits, result: Result<(), crate::DecodeError>) -> bool {
    exists|events: Seq<Part1ColdStorageEvent>| part1_bitmap_run(offset, records, layers, styles, limits, events) == Some((result, Seq::empty()))
}
pub(crate) open spec fn part1_bitmap_calls(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits) -> Seq<Part1ColdStorageEvent> {
    part1_mct_copy_normal_calls(part1_bitmap_requests(offset, records, layers, styles, limits))
}
pub(crate) proof fn part1_bitmap_normal(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits, tail: Seq<Part1ColdStorageEvent>)
    ensures part1_bitmap_result(offset, records, layers, styles, limits, part1_validate_progression_changes(offset, records, layers, styles, limits)),
        part1_bitmap_run(offset, records, layers, styles, limits, part1_bitmap_calls(offset, records, layers, styles, limits) + tail)
            == Some((part1_validate_progression_changes(offset, records, layers, styles, limits), tail)),
{
    reveal(part1_bitmap_result);
    let requests = part1_bitmap_requests(offset, records, layers, styles, limits);
    let calls = part1_bitmap_calls(offset, records, layers, styles, limits);
    part1_mct_copy_normal(requests, tail); part1_mct_copy_normal(requests, Seq::empty());
    assert(calls + Seq::<Part1ColdStorageEvent>::empty() =~= calls);
    assert(part1_bitmap_run(offset, records, layers, styles, limits, calls)
        == Some((part1_validate_progression_changes(offset, records, layers, styles, limits), Seq::empty())));
}
pub(crate) proof fn part1_bitmap_refused(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits)
    requires part1_mct_copy_result(part1_bitmap_requests(offset, records, layers, styles, limits), Err(crate::DecodeError::AllocationFailed)),
    ensures part1_bitmap_result(offset, records, layers, styles, limits, Err(crate::DecodeError::AllocationFailed)),
{
    reveal(part1_bitmap_result); reveal(part1_mct_copy_result);
    let calls = choose|calls: Seq<Part1ColdStorageEvent>| part1_mct_copy_run(part1_bitmap_requests(offset, records, layers, styles, limits), calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty()));
    assert(part1_bitmap_run(offset, records, layers, styles, limits, calls)
        == Some((Err(crate::DecodeError::AllocationFailed), Seq::empty())));
}
pub(crate) proof fn part1_bitmap_frame(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>, tail: Seq<Part1ColdStorageEvent>)
    requires part1_bitmap_run(offset, records, layers, styles, limits, events) == Some((result, rest)),
    ensures part1_bitmap_run(offset, records, layers, styles, limits, events + tail) == Some((result, rest + tail)),
{
    let requests = part1_bitmap_requests(offset, records, layers, styles, limits);
    if let Some((unit, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_frame(requests, events, unit, after, tail); }
}
pub(crate) proof fn part1_bitmap_projection(offset: usize, records: Seq<ProgressionChange>, layers: u16,
    styles: &ComponentCodingStyles, limits: &crate::ResourceLimits, events: Seq<Part1ColdStorageEvent>,
    result: Result<(), crate::DecodeError>, rest: Seq<Part1ColdStorageEvent>)
    requires part1_bitmap_run(offset, records, layers, styles, limits, events) == Some((result, rest)),
        result != Err(crate::DecodeError::AllocationFailed),
    ensures result == part1_validate_progression_changes(offset, records, layers, styles, limits),
{
    let requests = part1_bitmap_requests(offset, records, layers, styles, limits);
    if let Some((unit, after)) = part1_mct_copy_run(requests, events) { part1_mct_copy_projection(requests, events, unit, after); }
}

pub(crate) proof fn part1_cold_main_bitmap_error<'a>(initial: Part1CodestreamReader<'a>, input: Part1MainQuantizationInput<'a>, error: crate::DecodeError)
    requires part1_prepare_main_quantization(initial) == Ok(input),
        part1_finish_main_quantizations(input.raw.image_size.components, input.quantization, input.styles, input.raw.qcc).is_ok(),
        part1_bitmap_result(0, input.raw.progression, input.style.layers, &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, Err(error)),
    ensures part1_cold_layout_result(initial, Err(error)),
{
    reveal(part1_bitmap_result); reveal(part1_main_resolved_run); reveal(part1_cold_layout_result);
    let bitmap = choose|calls: Seq<Part1ColdStorageEvent>| part1_bitmap_run(0, input.raw.progression, input.style.layers,
        &crate::codestream::tile_part_native_styles(input.styles), input.reader.limits, calls) == Some((Err(error), Seq::empty()));
    let before = part1_prepare_main_progression_normal(initial);
    let quantization = part1_main_quantization_normal_calls(Ok(input));
    let calls = before + quantization + bitmap;
    assert(calls =~= before + (quantization + bitmap));
    assert(part1_prepare_main_progression_run(initial, calls) == Some((Ok(input), quantization + bitmap)));
    if quantization.len() == 0 { assert(quantization + bitmap =~= bitmap); }
    else { assert((quantization + bitmap).drop_first() =~= bitmap); }
    assert(part1_layout_with_cold_storage(initial, calls) == Some((Err(error), Seq::empty())));
}
pub(crate) proof fn part1_cold_tile_bitmap_error<'a>(input: Part1ColdTileInput<'a>,
    raw: Part1TileHeaderAccumulator, reader: Part1CodestreamReader<'a>, error: crate::DecodeError)
    requires part1_cold_tile_header(input) == (Ok(raw), reader),
        raw.pending_mct.len() == 0, raw.pending_mcc.len() == 0,
        match part1_finish_tile_components(input.components, raw.tile_coding_style, raw.tile_cod_seen, raw.coc_segments,
            raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles, input.quantizations, raw.part2_extensions, reader.limits) {
            Err(_) => false, Ok(configuration) => part1_bitmap_result(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers,
                &crate::codestream::tile_part_native_styles(configuration.0), reader.limits, Err(error)),
        },
    ensures part1_cold_tile_part_result(input, (Err(error), reader)),
{
    reveal(part1_bitmap_result); reveal(part1_cold_tile_part_result);
    let configuration = part1_finish_tile_components(input.components, raw.tile_coding_style, raw.tile_cod_seen, raw.coc_segments,
        raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles, input.quantizations, raw.part2_extensions, reader.limits)->Ok_0;
    let styles = crate::codestream::tile_part_native_styles(configuration.0);
    let bitmap = choose|calls: Seq<Part1ColdStorageEvent>| part1_bitmap_run(input.tile.0, raw.progression_changes, raw.tile_coding_style.layers,
        &styles, reader.limits, calls) == Some((Err(error), Seq::empty()));
    let before = part1_read_tile_progression_normal(input.reader, input.defaults.0, input.roi, input.progression,
        input.mct, input.extensions, input.components, input.tile.3, input.lengths, input.headers);
    part1_tile_components_cold_normal(input.components, raw.tile_coding_style, raw.tile_cod_seen, raw.coc_segments,
        raw.qcd_segment, input.defaults.1, raw.qcc_segments, input.styles, input.quantizations, raw.part2_extensions, reader.limits);
    let components = part1_cold_tile_configuration_calls(input);
    let calls = before + components + bitmap;
    assert(calls =~= before + (components + bitmap));
    assert(part1_cold_tile_part_run(input, calls) == Some(((Err(error), reader), Seq::empty())));
}

}
