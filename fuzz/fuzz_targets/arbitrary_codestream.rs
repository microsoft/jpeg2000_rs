#![no_main]

use jpeg2000_decoder::{
    DecodeOptions, codestream,
    decode::{
        decode_progression_prepared_image, derive_component_subbands,
        plan_progression_tile_at_with_component_overrides,
    },
    decode_codestream, decode_codestream_recover_missing_eoc,
    packet::decode_progression_tile_packets,
};
use jpeg2000_decoder_fuzz::resource_limits;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let limits = resource_limits();
    let options = DecodeOptions::new(limits);
    let _ = decode_codestream(data, &options);
    let _ = decode_codestream_recover_missing_eoc(data, &options);
    let Ok(layout) = codestream::parse_layout(data, &limits) else {
        return;
    };
    let Some(tile_part) = layout.tile_parts.first() else {
        return;
    };
    let mut component = 0_u16;
    while component < layout.info.image_size.components {
        if let (Ok(style), Ok(quantization)) = (
            tile_part.component_coding_styles.style(component),
            tile_part.component_quantizations.quantization(component),
        ) {
            let _ =
                derive_component_subbands(&layout.info.image_size, style, &quantization, component);
        }
        component += 1;
    }
    let Ok(mut plan) = plan_progression_tile_at_with_component_overrides(
        &layout.info.image_size,
        tile_part.tile_index,
        tile_part.coding_style,
        &tile_part.component_coding_styles,
        &tile_part.component_quantizations,
        &tile_part.roi_shifts,
        &limits,
    ) else {
        return;
    };
    let (grid, precincts) = plan.packet_execution();
    if decode_progression_tile_packets(&layout.tile_parts, grid, precincts, &limits).is_ok() {
        let _ = decode_progression_prepared_image(&layout.info.image_size, &plan, &limits);
    }
});
