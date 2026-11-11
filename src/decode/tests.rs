use super::api::{
    collect_nonlinear_regions, decode_codestream, decode_codestream_selected, decode_jp2,
    decode_jp2_color, decode_jp2_color_selected, decode_jp2_selected, decode_jph,
    decode_jpx_codestream, decode_jpx_codestream_color, decode_jpx_codestream_color_selected,
    decode_jpx_codestream_selected, decode_typed_layout, validate_part1_output_shape,
};
use super::arithmetic::{arithmetic_overflow, invalid_decode};
use super::code_blocks::{decode_code_block, decode_subband};
use super::execution::{
    account_planned_tile, apply_prepared_component_transform, collect_tile_parts,
    count_selected_component_blocks, decode_layout, decode_layout_selected,
    decode_planned_tile_components, decode_tile_parts_at, prepare_tile_decode_metadata,
    reconstruct_planned_tile, validate_part2_execution,
};
use super::geometry::{
    derive_component_subbands, derive_packet_grid_for_components, quantization_step_for_subband,
};
use super::output::{
    apply_associated_output, apply_jp2_output, color_selection_for_size, convert_associated_color,
    convert_associated_selected_color, convert_selected_color, copy_typed_component,
    finish_associated_selected_output, map_palette_component, palette_modulus,
};
use super::planning::{
    append_planned_codeblock, derive_planned_codeblock_geometry, derive_planned_precinct_origin,
    derive_planned_subband_lattice, plan_codeblock_decoders, plan_packet_precinct,
    plan_progression_tile, plan_progression_tile_at, plan_progression_tile_at_selected,
    plan_progression_tile_at_with_component_overrides, plan_progression_tile_at_with_roi,
    plan_subband_execution, plan_tile_component, prepare_component_plan_metadata,
    prepare_resolution_plan_metadata,
};
use super::reconstruction::{
    assemble_prepared_components, decode_progression_prepared_image, prepare_tile_component,
    prepare_tile_component_with_kernel, write_quantized_block,
};
use super::selection::validate_selection;
use super::*;
use crate::codestream::{ProgressionOrder, parse_layout};
use crate::packet::{
    CodeBlockPacketContext, CodeBlockPacketState, PacketBitReader, TagTree,
    decode_code_block_contribution, decode_progression_tile_packets,
};

#[path = "container_image_result_tests.rs"]
mod container_image_result;
#[path = "jpx_source_result_tests.rs"]
mod jpx_source_result;
#[path = "raw_typed_result_tests.rs"]
mod raw_typed_result;

fn reference_planned_block_geometry(
    grid: [u32; 4],
    clip: [u32; 4],
    block: [u32; 2],
) -> Result<(u32, u32, u16, u16), DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let checked = |value: u128| u32::try_from(value).map_err(|_| arithmetic);
    let ix = checked(u128::from(grid[0]) + u128::from(block[0]))?;
    let nx = checked(u128::from(ix) * u128::from(grid[2]))?;
    let iy = checked(u128::from(grid[1]) + u128::from(block[1]))?;
    let ny = checked(u128::from(iy) * u128::from(grid[3]))?;
    let x = nx.max(clip[0]);
    let y = ny.max(clip[1]);
    let ex = checked(u128::from(nx) + u128::from(grid[2]))?;
    let ey = checked(u128::from(ny) + u128::from(grid[3]))?;
    let width = u16::try_from(i64::from(ex.min(clip[2])) - i64::from(x)).map_err(|_| arithmetic)?;
    let height =
        u16::try_from(i64::from(ey.min(clip[3])) - i64::from(y)).map_err(|_| arithmetic)?;
    Ok((x, y, width, height))
}

#[test]
fn actual_planned_block_geometry_preserves_raw_lattice_clipping_and_u16_frontiers() {
    let words = [0, 1, 2, 65_535, 65_536, u32::MAX];
    let clips = [
        [0, 0, u32::MAX, u32::MAX],
        [0, 0, 0, 0],
        [1, 1, 65_535, 65_535],
        [u32::MAX, u32::MAX, 0, 0],
        [5, 7, 3, 1],
        [1, 3, 65_536, 65_537],
        [17, 31, 33, 65],
        [1, 1, u32::MAX, u32::MAX],
    ];
    let mut cases = 0;
    let mut zero_dimensions = 0;
    for first_x in words {
        for first_y in words {
            for width in words {
                for height in words {
                    for block_x in [0, 1, 2, u32::MAX] {
                        for block_y in [0, 1, 2, u32::MAX] {
                            for clip in clips {
                                let grid = [first_x, first_y, width, height];
                                let block = [block_x, block_y];
                                let expected = reference_planned_block_geometry(grid, clip, block);
                                assert_eq!(
                                    derive_planned_codeblock_geometry(grid, clip, block),
                                    expected
                                );
                                if let Ok((_, _, width, height)) = expected {
                                    zero_dimensions += usize::from(width == 0 || height == 0);
                                }
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 165_888);
    assert!(
        zero_dimensions > 100,
        "zero dimensions remain the decoder initializer's policy"
    );
}

#[test]
fn actual_precinct_origins_preserve_raw_divisor_addition_and_multiplication_frontiers() {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let words = [0, 1, 2, 65_535, 65_536, u32::MAX];
    let mut cases = 0;
    for x in words {
        for y in words {
            for across in words {
                for precinct in words {
                    for width in words {
                        for height in words {
                            let expected = if across == 0 {
                                Err(arithmetic)
                            } else {
                                let checked =
                                    |value: u128| u32::try_from(value).map_err(|_| arithmetic);
                                (|| {
                                    let x = checked(u128::from(x) + u128::from(precinct % across))?;
                                    let y = checked(u128::from(y) + u128::from(precinct / across))?;
                                    let bx = checked(u128::from(x) * u128::from(width))?;
                                    let by = checked(u128::from(y) * u128::from(height))?;
                                    Ok([bx, by])
                                })()
                            };
                            assert_eq!(
                                derive_planned_precinct_origin(
                                    [x, y],
                                    across,
                                    precinct,
                                    [width, height]
                                ),
                                expected
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 46_656);
}

fn raw_planned_subband(
    x0: u32,
    y0: u32,
    bits: u16,
    orientation: SubbandOrientation,
) -> SubbandGeometry {
    SubbandGeometry {
        resolution: u8::MAX,
        orientation,
        x0,
        y0,
        width: u32::MAX,
        height: 0,
        resolution_width: 0,
        resolution_height: u32::MAX,
        quantization_index: u16::MAX,
        quantization_step: QuantizationStep {
            exponent: u8::MAX,
            mantissa: u16::MAX,
        },
        dynamic_range: u8::MAX,
        significant_bitplanes: bits,
        roi_shift: u8::MAX,
        low_pass_first_x: true,
        low_pass_first_y: false,
    }
}

#[allow(clippy::too_many_arguments)]
fn reference_planned_cell(
    grid: [u32; 4],
    clip: [u32; 4],
    block: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize),
    mut state: PlannedCodeBlocks,
) -> Result<PlannedCodeBlocks, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let (x, y, width, height) = reference_planned_block_geometry(grid, clip, block)?;
    let mut decoder = Tier1CodeBlockDecoder::new(
        width,
        height,
        subband.significant_bitplanes,
        subband.orientation,
        style,
    )?;
    decoder.set_multiple_ht_sets_allowed(policy.0);
    decoder.set_ht_magnitude_bound(policy.1)?;
    let x = u32::try_from(i64::from(x) - i64::from(subband.x0)).map_err(|_| arithmetic)?;
    let y = u32::try_from(i64::from(y) - i64::from(subband.y0)).map_err(|_| arithmetic)?;
    let next = usize::try_from(state.decoder_index as u128 + 1).map_err(|_| arithmetic)?;
    state.placements.push(ProgressionCodeBlockPlacement {
        precinct_index: indices.0,
        decoder_index: state.decoder_index,
        subband_index: indices.1,
        x,
        y,
    });
    state.decoders.push(decoder);
    state.decoder_index = next;
    Ok(state)
}

#[allow(clippy::too_many_arguments)]
fn reference_planned_codeblocks(
    grid: [u32; 4],
    clip: [u32; 4],
    blocks: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    total: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedCodeBlocks, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let count = u64::from(blocks[0]) * u64::from(blocks[1]);
    let total = if selected {
        let next = u64::try_from(u128::from(total) + u128::from(count)).map_err(|_| arithmetic)?;
        if next > limits.maximum_code_blocks() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::CodeBlocks,
                limit: limits.maximum_code_blocks(),
                actual: next,
            });
        }
        if next > limits.maximum_work_units() {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::WorkUnits,
                limit: limits.maximum_work_units(),
                actual: next,
            });
        }
        next
    } else {
        total
    };
    usize::try_from(count).map_err(|_| arithmetic)?;
    let mut state = PlannedCodeBlocks {
        decoders: Vec::new(),
        placements,
        decoder_index: indices.2,
        planned_code_blocks: total,
    };
    for index in 0..count {
        let block = [
            u32::try_from(index % u64::from(blocks[0])).unwrap(),
            u32::try_from(index / u64::from(blocks[0])).unwrap(),
        ];
        state = reference_planned_cell(
            grid,
            clip,
            block,
            subband,
            style,
            policy,
            (indices.0, indices.1),
            state,
        )?;
    }
    Ok(state)
}

fn assert_planned_blocks_equal(
    actual: Result<PlannedCodeBlocks, DecodeError>,
    expected: Result<PlannedCodeBlocks, DecodeError>,
) -> bool {
    match (actual, expected) {
        (Err(actual), Err(expected)) => {
            assert_eq!(actual, expected);
            false
        }
        (Ok(actual), Ok(expected)) => {
            assert_eq!(actual.placements, expected.placements);
            assert_eq!(actual.decoder_index, expected.decoder_index);
            assert_eq!(actual.planned_code_blocks, expected.planned_code_blocks);
            assert_eq!(
                format!("{:?}", actual.decoders),
                format!("{:?}", expected.decoders)
            );
            true
        }
        (Err(error), Ok(_)) => panic!("unexpected plan error: {error:?}"),
        (Ok(_), Err(error)) => panic!("plan should have failed: {error:?}"),
    }
}

#[test]
fn actual_codeblock_vectors_bind_every_decoder_placement_prefix_policy_and_selected_limit() {
    let grids = [
        [0, 0, 1, 1],
        [1, 2, 2, 3],
        [0, 0, 0, 1],
        [0, 0, 65, 64],
        [u32::MAX, 0, 2, 1],
        [0, 0, 65_536, 1],
    ];
    let mut cases = 0;
    let mut successes = 0;
    for grid in grids {
        for clip in [[0, 0, 16, 16], [1, 2, 7, 9], [0, 0, u32::MAX, u32::MAX]] {
            for blocks in [[0, 0], [0, 2], [1, 1], [2, 1], [2, 3]] {
                for (x0, y0, bits) in [
                    (0, 0, 0),
                    (0, 0, 1),
                    (1, 2, 2),
                    (u32::MAX, u32::MAX, 74),
                    (0, 0, 74),
                    (0, 0, 75),
                ] {
                    for orientation in [SubbandOrientation::Ll, SubbandOrientation::Hh] {
                        let subband = raw_planned_subband(x0, y0, bits, orientation);
                        let style = Tier1CodingStyle {
                            force_high_throughput: true,
                            segmentation_symbols: true,
                            block_coding: if bits == 1 {
                                crate::tier1::Tier1BlockCoding::HighThroughput
                            } else {
                                crate::tier1::Tier1BlockCoding::Mixed
                            },
                            ..Tier1CodingStyle::default()
                        };
                        for policy in [(false, 0), (false, 74), (true, 1), (true, 75)] {
                            for selected in [false, true] {
                                for (total, block_limit, work_limit) in
                                    [(0, 100, 100), (0, 0, 0), (1, 2, 1), (u64::MAX, 100, 100)]
                                {
                                    let limits = ResourceLimits::HARDENED
                                        .with_maximum_code_blocks(block_limit)
                                        .unwrap()
                                        .with_maximum_work_units(work_limit)
                                        .unwrap();
                                    for indices in [
                                        (17, 31, 0),
                                        (usize::MAX, usize::MAX, 3),
                                        (4, 7, usize::MAX),
                                    ] {
                                        let prefix = vec![ProgressionCodeBlockPlacement {
                                            precinct_index: usize::MAX,
                                            decoder_index: usize::MAX,
                                            subband_index: usize::MAX,
                                            x: u32::MAX,
                                            y: u32::MAX,
                                        }];
                                        let expected = reference_planned_codeblocks(
                                            grid,
                                            clip,
                                            blocks,
                                            subband,
                                            style,
                                            policy,
                                            indices,
                                            prefix.clone(),
                                            total,
                                            selected,
                                            &limits,
                                        );
                                        let actual = plan_codeblock_decoders(
                                            grid, clip, blocks, subband, style, policy, indices,
                                            prefix, total, selected, &limits,
                                        );
                                        successes += usize::from(assert_planned_blocks_equal(
                                            actual, expected,
                                        ));
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 103_680);
    assert!(successes > 1_000);
    for blocks in [[u32::MAX, 0], [u32::MAX, u32::MAX]] {
        let subband = raw_planned_subband(0, 0, 0, SubbandOrientation::Ll);
        let limits = ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap();
        let expected = reference_planned_codeblocks(
            [0; 4],
            [0; 4],
            blocks,
            subband,
            Tier1CodingStyle::default(),
            (true, 0),
            (0, 0, usize::MAX),
            Vec::new(),
            0,
            true,
            &limits,
        );
        let actual = plan_codeblock_decoders(
            [0; 4],
            [0; 4],
            blocks,
            subband,
            Tier1CodingStyle::default(),
            (true, 0),
            (0, 0, usize::MAX),
            Vec::new(),
            0,
            true,
            &limits,
        );
        assert_planned_blocks_equal(actual, expected);
    }
}

#[test]
fn actual_codeblock_cell_retains_existing_owned_decoder_and_placement_buffers() {
    let mut cases = 0;
    for block in [[0, 0], [1, 2], [u32::MAX, 0], [0, u32::MAX]] {
        for origin in [0, 1, u32::MAX] {
            for bits in [0, 1, 74, 75] {
                for flattened in [0, 1, usize::MAX - 1, usize::MAX] {
                    for bound in [0, 1, 74, 75] {
                        let style = Tier1CodingStyle::default();
                        let seed = || PlannedCodeBlocks {
                            decoders: vec![
                                Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Hh, style)
                                    .unwrap(),
                            ],
                            placements: vec![ProgressionCodeBlockPlacement {
                                precinct_index: 19,
                                decoder_index: usize::MAX,
                                subband_index: 37,
                                x: u32::MAX,
                                y: 7,
                            }],
                            decoder_index: flattened,
                            planned_code_blocks: u64::MAX,
                        };
                        let subband =
                            raw_planned_subband(origin, origin, bits, SubbandOrientation::Lh);
                        let expected = reference_planned_cell(
                            [0, 0, 1, 1],
                            [0, 0, 5, 5],
                            block,
                            subband,
                            style,
                            (true, bound),
                            (usize::MAX, 31),
                            seed(),
                        );
                        let actual = append_planned_codeblock(
                            [0, 0, 1, 1],
                            [0, 0, 5, 5],
                            block,
                            subband,
                            style,
                            (true, bound),
                            (usize::MAX, 31),
                            seed(),
                        );
                        assert_planned_blocks_equal(actual, expected);
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 768);
}

fn reference_subband_lattice(
    band: [u32; 4],
    block_size: [u32; 2],
    subband: SubbandGeometry,
) -> Result<Option<PlannedSubbandLattice>, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let checked = |value: u128| u32::try_from(value).map_err(|_| arithmetic);
    let sx = subband.x0.max(band[0]);
    let sy = subband.y0.max(band[1]);
    let sx1 = checked(u128::from(subband.x0) + u128::from(subband.width))?;
    let sy1 = checked(u128::from(subband.y0) + u128::from(subband.height))?;
    if sx >= sx1 || sy >= sy1 {
        return Ok(None);
    }
    let ex = checked(u128::from(band[0]) + u128::from(band[2]))?.min(sx1);
    let ey = checked(u128::from(band[1]) + u128::from(band[3]))?.min(sy1);
    if sx >= ex || sy >= ey {
        return Ok(None);
    }
    if block_size[0] == 0 || block_size[1] == 0 {
        return Err(invalid);
    }
    let fx = sx / block_size[0];
    let fy = sy / block_size[1];
    let across = u32::try_from(i64::from(ex.div_ceil(block_size[0])) - i64::from(fx))
        .map_err(|_| arithmetic)?;
    let down = u32::try_from(i64::from(ey.div_ceil(block_size[1])) - i64::from(fy))
        .map_err(|_| arithmetic)?;
    Ok(Some(PlannedSubbandLattice {
        grid: [fx, fy, block_size[0], block_size[1]],
        clip: [sx, sy, ex, ey],
        blocks: [across, down],
    }))
}

#[test]
fn sarah_dev_76bf9f9717_empty_geometry_is_not_a_subband_lattice() {
    let mut subband = raw_planned_subband(0, 0, 0, SubbandOrientation::Hh);
    subband.width = 14;
    subband.height = 8;
    assert_eq!(
        derive_planned_subband_lattice([2, 0, 0, 4], [0, 0], subband),
        Ok(None),
    );
    assert_eq!(
        derive_planned_subband_lattice([2, 1, 0, u32::MAX], [0, 0], subband),
        Err(arithmetic_overflow()),
    );
    assert_eq!(
        derive_planned_subband_lattice([u32::MAX, 0, 1, 4], [0, 0], subband),
        Ok(None),
    );
    assert_eq!(
        derive_planned_subband_lattice([0, 0, 2, 2], [0, 0], subband),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::InvalidCodeBlock,
        }),
    );
    let mut cases = 0;
    for bx in 0_u32..6 {
        for by in 0_u32..6 {
            for bw in 0_u32..5 {
                for bh in 0_u32..5 {
                    for (sx, sy) in [(0_u32, 0), (2, 1)] {
                        for (sw, sh) in [(0_u32, 0), (1, 1), (3, 2), (7, 8)] {
                            let mut subband =
                                raw_planned_subband(sx, sy, 0, SubbandOrientation::Hh);
                            subband.width = sw;
                            subband.height = sh;
                            let lo = [u64::from(bx.max(sx)), u64::from(by.max(sy))];
                            let hi = [
                                (u64::from(bx) + u64::from(bw)).min(u64::from(sx) + u64::from(sw)),
                                (u64::from(by) + u64::from(bh)).min(u64::from(sy) + u64::from(sh)),
                            ];
                            for block in [1_u32, 2, 4, 64] {
                                let actual = derive_planned_subband_lattice(
                                    [bx, by, bw, bh],
                                    [block, block],
                                    subband,
                                )
                                .unwrap();
                                if lo[0] >= hi[0] || lo[1] >= hi[1] {
                                    assert!(
                                        actual.is_none(),
                                        "band={bx},{by},{bw},{bh} subband={sx},{sy},{sw},{sh} block={block}"
                                    );
                                } else {
                                    let lattice =
                                        actual.expect("nonempty rectangle needs its lattice");
                                    assert_eq!(
                                        lattice.clip,
                                        [lo[0] as u32, lo[1] as u32, hi[0] as u32, hi[1] as u32],
                                    );
                                    let step = u64::from(block);
                                    assert_eq!(
                                        lattice.blocks,
                                        [
                                            u32::try_from(hi[0].div_ceil(step) - lo[0] / step)
                                                .unwrap(),
                                            u32::try_from(hi[1].div_ceil(step) - lo[1] / step)
                                                .unwrap(),
                                        ]
                                    );
                                    assert!(lattice.blocks[0] > 0 && lattice.blocks[1] > 0);
                                }
                                cases += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 28_800);
}

#[test]
fn sarah_dev_76bf9f9717_empty_geometry_has_zero_grid_axes() {
    let bytes = two_tile_codestream();
    let limits = ResourceLimits::default();
    let mut layout = parse_layout(&bytes, &limits).unwrap();
    let style = CodingStyle {
        decomposition_levels: 3,
        ..layout.info.coding_style
    };
    for origin in [[0_u32, 0], [1, 0], [0, 1], [1, 1], [3, 5]] {
        let size = &mut layout.info.image_size;
        size.width = 1;
        size.height = 1;
        size.x_origin = origin[0];
        size.y_origin = origin[1];
        size.tile_width = 8;
        size.tile_height = 8;
        size.tile_x_origin = 0;
        size.tile_y_origin = 0;
        size.tiles_across = 1;
        size.tiles_down = 1;
        for resolution in 0..=3 {
            let actual = derive_component_resolution_geometry(size, style, 0, resolution).unwrap();
            let scale = 1_u32 << (3 - resolution);
            let width = (origin[0] + 1).div_ceil(scale) - origin[0].div_ceil(scale);
            let height = (origin[1] + 1).div_ceil(scale) - origin[1].div_ceil(scale);
            assert_eq!((actual.width, actual.height), (width, height));
            assert_eq!(
                actual.code_blocks_across, width,
                "origin={origin:?} resolution={resolution}"
            );
            assert_eq!(actual.code_blocks_down, height);
            assert_eq!(actual.code_blocks, u64::from(width) * u64::from(height));
            assert_eq!(
                (actual.precincts_across, actual.precincts_down),
                (width, height)
            );
            assert_eq!(actual.precincts, u64::from(width) * u64::from(height));
        }
    }
}

#[test]
fn actual_subband_lattice_preserves_raw_overflow_empty_intersection_and_divisor_policy() {
    let origins = [
        (0, 0),
        (1, 2),
        (17, 31),
        (u32::MAX, 0),
        (0, u32::MAX),
        (u32::MAX, u32::MAX),
    ];
    let extents = [
        (0, 0),
        (1, 2),
        (17, 31),
        (65_535, 65_536),
        (65_536, 65_535),
        (u32::MAX, u32::MAX),
    ];
    let mut cases = 0;
    let mut empty = 0;
    let mut nonempty = 0;
    for (bx, by) in origins {
        for (bw, bh) in extents {
            for block in [
                [0, 0],
                [0, 1],
                [1, 0],
                [1, 1],
                [2, 3],
                [64, 65],
                [65_535, 65_536],
                [u32::MAX, u32::MAX],
            ] {
                for (sx, sy) in origins {
                    for (sw, sh) in extents {
                        let mut subband = raw_planned_subband(sx, sy, 0, SubbandOrientation::Hh);
                        subband.width = sw;
                        subband.height = sh;
                        let band = [bx, by, bw, bh];
                        let expected = reference_subband_lattice(band, block, subband);
                        assert_eq!(
                            derive_planned_subband_lattice(band, block, subband),
                            expected
                        );
                        empty += usize::from(matches!(expected, Ok(None)));
                        nonempty += usize::from(matches!(expected, Ok(Some(_))));
                        cases += 1;
                    }
                }
            }
        }
    }
    assert_eq!(cases, 10_368);
    assert!(empty > 100 && nonempty > 100);
}

#[allow(clippy::too_many_arguments)]
fn reference_subband_execution(
    band: [u32; 4],
    block_size: [u32; 2],
    subband: SubbandGeometry,
    style: Tier1CodingStyle,
    policy: (bool, u8),
    indices: (usize, usize, usize),
    placements: Vec<ProgressionCodeBlockPlacement>,
    total: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedSubbandExecution, DecodeError> {
    let Some(lattice) = reference_subband_lattice(band, block_size, subband)? else {
        return Ok(PlannedSubbandExecution {
            execution: None,
            placements,
            decoder_index: indices.2,
            planned_code_blocks: total,
        });
    };
    let planned = reference_planned_codeblocks(
        lattice.grid,
        lattice.clip,
        lattice.blocks,
        subband,
        style,
        policy,
        indices,
        placements,
        total,
        selected,
        limits,
    )?;
    Ok(PlannedSubbandExecution {
        execution: Some(PacketSubbandExecution {
            orientation: subband.orientation,
            code_blocks_across: lattice.blocks[0],
            code_blocks_down: lattice.blocks[1],
            maximum_zero_bitplanes: subband.significant_bitplanes,
            decoders: planned.decoders,
        }),
        placements: planned.placements,
        decoder_index: planned.decoder_index,
        planned_code_blocks: planned.planned_code_blocks,
    })
}

#[test]
fn actual_subband_execution_derives_full_packet_row_and_preserves_lazy_owned_prefix() {
    let mut cases = 0;
    let mut empty = 0;
    let mut populated = 0;
    for band in [
        [0, 0, 0, 0],
        [0, 0, 2, 3],
        [1, 2, 3, 4],
        [u32::MAX, u32::MAX, 1, 1],
        [0, 0, u32::MAX, u32::MAX],
    ] {
        for (x, y, w, h) in [
            (0, 0, 0, 0),
            (0, 0, 1, 1),
            (1, 2, 3, 2),
            (2, 1, 1, 3),
            (u32::MAX, 0, 1, 1),
            (0, u32::MAX, 1, 1),
        ] {
            for block in [[0, 1], [1, 0], [1, 1], [2, 3], [65, 64]] {
                for bits in [0, 1, 74, 75] {
                    let mut subband = raw_planned_subband(x, y, bits, SubbandOrientation::Lh);
                    subband.width = w;
                    subband.height = h;
                    let style = Tier1CodingStyle {
                        force_high_throughput: true,
                        block_coding: crate::tier1::Tier1BlockCoding::Mixed,
                        ..Tier1CodingStyle::default()
                    };
                    for policy in [(false, 0), (false, 74), (true, 1), (true, 75)] {
                        for selected in [false, true] {
                            for (total, block_limit, work_limit) in
                                [(0, 100, 100), (0, 0, 0), (1, 2, 1), (u64::MAX, 100, 100)]
                            {
                                let limits = ResourceLimits::HARDENED
                                    .with_maximum_code_blocks(block_limit)
                                    .unwrap()
                                    .with_maximum_work_units(work_limit)
                                    .unwrap();
                                for indices in
                                    [(17, 31, 0), (usize::MAX, usize::MAX, 3), (4, 7, usize::MAX)]
                                {
                                    let prefix = vec![ProgressionCodeBlockPlacement {
                                        precinct_index: usize::MAX,
                                        decoder_index: usize::MAX,
                                        subband_index: usize::MAX,
                                        x: u32::MAX,
                                        y: u32::MAX,
                                    }];
                                    let expected = reference_subband_execution(
                                        band,
                                        block,
                                        subband,
                                        style,
                                        policy,
                                        indices,
                                        prefix.clone(),
                                        total,
                                        selected,
                                        &limits,
                                    );
                                    let actual = plan_subband_execution(
                                        band, block, subband, style, policy, indices, prefix,
                                        total, selected, &limits,
                                    );
                                    match (actual, expected) {
                                        (Err(actual), Err(expected)) => {
                                            assert_eq!(actual, expected)
                                        }
                                        (Ok(actual), Ok(expected)) => {
                                            assert_eq!(actual.placements, expected.placements);
                                            assert_eq!(
                                                actual.decoder_index,
                                                expected.decoder_index
                                            );
                                            assert_eq!(
                                                actual.planned_code_blocks,
                                                expected.planned_code_blocks
                                            );
                                            match (actual.execution, expected.execution) {
                                                (None, None) => empty += 1,
                                                (Some(actual), Some(expected)) => {
                                                    assert_eq!(
                                                        actual.orientation,
                                                        expected.orientation
                                                    );
                                                    assert_eq!(
                                                        actual.code_blocks_across,
                                                        expected.code_blocks_across
                                                    );
                                                    assert_eq!(
                                                        actual.code_blocks_down,
                                                        expected.code_blocks_down
                                                    );
                                                    assert_eq!(
                                                        actual.maximum_zero_bitplanes,
                                                        expected.maximum_zero_bitplanes
                                                    );
                                                    populated +=
                                                        usize::from(!actual.decoders.is_empty());
                                                    assert_eq!(
                                                        format!("{:?}", actual.decoders),
                                                        format!("{:?}", expected.decoders)
                                                    );
                                                }
                                                _ => panic!(
                                                    "wrong presence of packet subband execution"
                                                ),
                                            }
                                        }
                                        (Err(error), Ok(_)) => {
                                            panic!("unexpected subband error: {error:?}")
                                        }
                                        (Ok(_), Err(error)) => {
                                            panic!("subband should have failed: {error:?}")
                                        }
                                    }
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 57_600);
    assert!(empty > 100 && populated > 100);
}

#[allow(clippy::too_many_arguments)]
fn reference_planned_precinct(
    band: [u32; 4],
    block_size: [u32; 2],
    subbands: &[SubbandGeometry],
    range: (usize, usize),
    style: Tier1CodingStyle,
    policy: (bool, u8),
    location: (u16, u8, u32, usize),
    mut placements: Vec<ProgressionCodeBlockPlacement>,
    mut total: u64,
    selected: bool,
    limits: &ResourceLimits,
) -> Result<PlannedPrecinct, DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let mut executions = Vec::new();
    let mut flattened = 0;
    for local in 0..range.1 {
        let index = usize::try_from(range.0 as u128 + local as u128).map_err(|_| arithmetic)?;
        let subband = *subbands.get(index).ok_or(invalid)?;
        let planned = reference_subband_execution(
            band,
            block_size,
            subband,
            style,
            policy,
            (location.3, index, flattened),
            placements,
            total,
            selected,
            limits,
        )?;
        placements = planned.placements;
        flattened = planned.decoder_index;
        total = planned.planned_code_blocks;
        if let Some(execution) = planned.execution {
            executions.push(execution);
        }
    }
    let precinct = PacketPrecinctDecoder::new_subbands(
        location.0, location.1, location.2, style, executions, limits,
    )?;
    Ok(PlannedPrecinct {
        precinct,
        placements,
        planned_code_blocks: total,
    })
}

#[test]
fn actual_precinct_plan_derives_all_private_packet_fields_from_raw_subband_ranges() {
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(2)
            .unwrap()
            .with_maximum_work_units(1)
            .unwrap(),
    ];
    let mut cases = 0;
    let mut populated = 0;
    let mut empty = 0;
    for physical in [0, 1, 3, 4] {
        for variant in 0..4 {
            let subbands = (0..physical)
                .map(|index| {
                    let mut subband = raw_planned_subband(
                        0,
                        0,
                        1,
                        [
                            SubbandOrientation::Ll,
                            SubbandOrientation::Hl,
                            SubbandOrientation::Lh,
                            SubbandOrientation::Hh,
                        ][index],
                    );
                    match variant {
                        0 => {
                            subband.width = 1;
                            subband.height = 1;
                        }
                        1 => {
                            subband.width = 0;
                            subband.height = 1;
                            subband.significant_bitplanes = 0;
                        }
                        2 => {
                            subband.x0 = u32::try_from(index % 2).unwrap();
                            subband.width = 2;
                            subband.height = 3;
                            subband.significant_bitplanes = 74;
                        }
                        _ => {
                            subband.x0 = u32::MAX;
                            subband.width = 1;
                            subband.height = 1;
                            subband.significant_bitplanes = 75;
                        }
                    }
                    subband
                })
                .collect::<Vec<_>>();
            let style = Tier1CodingStyle {
                force_high_throughput: true,
                reset_contexts: true,
                block_coding: crate::tier1::Tier1BlockCoding::Mixed,
                ..Tier1CodingStyle::default()
            };
            for count in [0, 1, 3, 4, 5] {
                for first in [0, 1, usize::MAX] {
                    for band in [[0, 0, 4, 4], [17, 31, 1, 1]] {
                        for block in [[0, 1], [1, 1], [2, 3]] {
                            for policy in [(false, 0), (true, 1)] {
                                for selected in [false, true] {
                                    for limit in &limits {
                                        for location in [
                                            (0, 0, 0, 0),
                                            (u16::MAX, u8::MAX, u32::MAX, usize::MAX),
                                        ] {
                                            for total in [0, u64::MAX] {
                                                let prefix = vec![ProgressionCodeBlockPlacement {
                                                    precinct_index: 19,
                                                    decoder_index: usize::MAX,
                                                    subband_index: 37,
                                                    x: u32::MAX,
                                                    y: 7,
                                                }];
                                                let expected = reference_planned_precinct(
                                                    band,
                                                    block,
                                                    &subbands,
                                                    (first, count),
                                                    style,
                                                    policy,
                                                    location,
                                                    prefix.clone(),
                                                    total,
                                                    selected,
                                                    limit,
                                                );
                                                let actual = plan_packet_precinct(
                                                    band,
                                                    block,
                                                    &subbands,
                                                    (first, count),
                                                    style,
                                                    policy,
                                                    location,
                                                    prefix,
                                                    total,
                                                    selected,
                                                    limit,
                                                );
                                                match (actual, expected) {
                                                    (Err(actual), Err(expected)) => {
                                                        assert_eq!(actual, expected)
                                                    }
                                                    (Ok(actual), Ok(expected)) => {
                                                        assert_eq!(
                                                            actual.placements,
                                                            expected.placements
                                                        );
                                                        assert_eq!(
                                                            actual.planned_code_blocks,
                                                            expected.planned_code_blocks
                                                        );
                                                        let is_empty =
                                                            actual.precinct.decoders().is_empty();
                                                        empty += usize::from(is_empty);
                                                        populated += usize::from(!is_empty);
                                                        assert_eq!(crate::packet::exact_packet_precinct_snapshot(&actual.precinct), crate::packet::exact_packet_precinct_snapshot(&expected.precinct));
                                                    }
                                                    (Err(error), Ok(_)) => panic!(
                                                        "unexpected precinct-plan error: {error:?}"
                                                    ),
                                                    (Ok(_), Err(error)) => panic!(
                                                        "precinct plan should have failed: {error:?}"
                                                    ),
                                                }
                                                cases += 1;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 92_160);
    assert!(empty > 100 && populated > 100);
}

fn planning_prefix(present: bool) -> Vec<PacketPrecinctDecoder> {
    if !present {
        return Vec::new();
    }
    let style = Tier1CodingStyle::default();
    vec![
        PacketPrecinctDecoder::new_subbands(
            19,
            u8::MAX,
            u32::MAX,
            style,
            vec![PacketSubbandExecution {
                orientation: SubbandOrientation::Hh,
                code_blocks_across: 1,
                code_blocks_down: 1,
                maximum_zero_bitplanes: 2,
                decoders: vec![
                    Tier1CodeBlockDecoder::new(1, 1, 2, SubbandOrientation::Hh, style).unwrap(),
                ],
            }],
            &ResourceLimits::HARDENED,
        )
        .unwrap(),
    ]
}

fn planning_fixture_owners<'a>(
    layout: &'a CodestreamLayout<'_>,
    tile_scope: bool,
) -> (
    &'a ComponentCodingStyles,
    &'a ComponentQuantizations,
    &'a RoiShifts,
) {
    if tile_scope {
        let tile = &layout.tile_parts[0];
        (
            &tile.component_coding_styles,
            &tile.component_quantizations,
            &tile.roi_shifts,
        )
    } else {
        (
            &layout.info.component_coding_styles,
            &layout.info.component_quantizations,
            &layout.info.roi_shifts,
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn reference_component_plan(
    size: &ImageSize,
    styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi: &RoiShifts,
    component: u16,
    selection: (u16, u8),
    policy: (bool, u8, bool),
    mut precincts: Vec<PacketPrecinctDecoder>,
    mut total: u64,
    limits: &ResourceLimits,
) -> Result<PlannedComponent, DecodeError> {
    let metadata = prepare_component_plan_metadata(
        size,
        styles,
        quantizations,
        roi,
        component,
        selection,
        policy.2,
    )?;
    let mut placements = Vec::new();
    for resolution in 0..=u16::from(metadata.component_coding_style.decomposition_levels) {
        let resolution = u8::try_from(resolution).unwrap();
        let data = prepare_resolution_plan_metadata(
            size,
            metadata.component_coding_style,
            component,
            (selection.0, resolution),
            [metadata.bounds.x0, metadata.bounds.y0],
        )?;
        for precinct in 0..data.precincts_in_resolution {
            let origin = derive_planned_precinct_origin(
                data.first_precinct,
                data.geometry.precincts_across,
                precinct,
                data.band_size,
            )?;
            let planned = reference_planned_precinct(
                [origin[0], origin[1], data.band_size[0], data.band_size[1]],
                data.block_size,
                &metadata.subbands,
                (data.first_subband, data.subband_count),
                metadata.tier1_style,
                (policy.0, policy.1),
                (component, resolution, precinct, precincts.len()),
                placements,
                total,
                resolution <= metadata.output_resolution,
                limits,
            )?;
            placements = planned.placements;
            total = planned.planned_code_blocks;
            precincts.push(planned.precinct);
        }
        if resolution == u8::MAX {
            return Err(arithmetic_overflow());
        }
    }
    Ok(PlannedComponent {
        component: PlannedTileComponent {
            component,
            x: metadata.component_x,
            y: metadata.component_y,
            width: metadata.component_width,
            height: metadata.component_height,
            output_resolution: metadata.output_resolution,
            subbands: metadata.subbands,
            placements,
        },
        precincts,
        planned_code_blocks: total,
    })
}

#[allow(clippy::too_many_arguments)]
fn reference_tile_plan(
    size: &ImageSize,
    coding_style: CodingStyle,
    styles: &ComponentCodingStyles,
    quantizations: &ComponentQuantizations,
    roi: &RoiShifts,
    selection: (u16, u8),
    policy: (bool, u8, bool),
    limits: &ResourceLimits,
) -> Result<ProgressionTilePlan, DecodeError> {
    size.tile_bounds(selection.0)?;
    let grid = derive_packet_grid_for_components(
        size,
        styles,
        coding_style.layers,
        limits,
        Some(selection.0),
        selection.1,
    )?;
    let mut precincts = Vec::new();
    let mut components = Vec::new();
    let mut total = 0;
    for component in 0..size.components {
        let planned = reference_component_plan(
            size,
            styles,
            quantizations,
            roi,
            component,
            selection,
            policy,
            precincts,
            total,
            limits,
        )?;
        precincts = planned.precincts;
        total = planned.planned_code_blocks;
        components.push(planned.component);
    }
    Ok(ProgressionTilePlan {
        tile_index: selection.0,
        coding_style,
        component_coding_styles: *styles,
        grid,
        precincts,
        components,
    })
}

fn assert_tile_plans_equal(
    actual: Result<ProgressionTilePlan, DecodeError>,
    expected: Result<ProgressionTilePlan, DecodeError>,
) -> bool {
    match (actual, expected) {
        (Err(actual), Err(expected)) => {
            assert_eq!(actual, expected);
            false
        }
        (Ok(actual), Ok(expected)) => {
            assert_eq!(actual.tile_index, expected.tile_index);
            assert_eq!(actual.coding_style, expected.coding_style);
            assert_eq!(
                actual.component_coding_styles,
                expected.component_coding_styles
            );
            assert_eq!(actual.grid, expected.grid);
            assert_eq!(actual.components, expected.components);
            assert_eq!(
                actual
                    .precincts
                    .iter()
                    .map(crate::packet::exact_packet_precinct_snapshot)
                    .collect::<Vec<_>>(),
                expected
                    .precincts
                    .iter()
                    .map(crate::packet::exact_packet_precinct_snapshot)
                    .collect::<Vec<_>>()
            );
            true
        }
        (Err(error), Ok(_)) => panic!("unexpected tile-plan error: {error:?}"),
        (Ok(_), Err(error)) => panic!("tile plan should have failed: {error:?}"),
    }
}

#[test]
fn actual_component_plan_derives_full_component_and_precinct_vectors_from_real_raw_owners() {
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(2)
            .unwrap()
            .with_maximum_work_units(1)
            .unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        for tile_scope in [false, true] {
            let (styles, quantizations, roi) = planning_fixture_owners(&layout, tile_scope);
            for component in [0, 1, 64] {
                for tile in [0, 1, u16::MAX] {
                    for discard in [0, 1, 2, 3, u8::MAX] {
                        for policy in [
                            (false, 0, false),
                            (false, 74, false),
                            (true, 1, true),
                            (true, 75, true),
                        ] {
                            for limit in &limits {
                                for total in [0, 1, u64::MAX] {
                                    for prefix in [false, true] {
                                        let expected = reference_component_plan(
                                            &layout.info.image_size,
                                            styles,
                                            quantizations,
                                            roi,
                                            component,
                                            (tile, discard),
                                            policy,
                                            planning_prefix(prefix),
                                            total,
                                            limit,
                                        );
                                        let actual = plan_tile_component(
                                            &layout.info.image_size,
                                            styles,
                                            quantizations,
                                            roi,
                                            component,
                                            (tile, discard),
                                            policy,
                                            planning_prefix(prefix),
                                            total,
                                            limit,
                                        );
                                        match (actual, expected) {
                                            (Err(actual), Err(expected)) => {
                                                assert_eq!(actual, expected)
                                            }
                                            (Ok(actual), Ok(expected)) => {
                                                assert_eq!(actual.component, expected.component);
                                                assert_eq!(
                                                    actual.planned_code_blocks,
                                                    expected.planned_code_blocks
                                                );
                                                assert_eq!(actual.precincts.iter().map(crate::packet::exact_packet_precinct_snapshot).collect::<Vec<_>>(),
                                                        expected.precincts.iter().map(crate::packet::exact_packet_precinct_snapshot).collect::<Vec<_>>());
                                                successes += 1;
                                            }
                                            (Err(error), Ok(_)) => {
                                                panic!("unexpected component-plan error: {error:?}")
                                            }
                                            (Ok(_), Err(error)) => panic!(
                                                "component plan should have failed: {error:?}"
                                            ),
                                        }
                                        cases += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 25_920);
    assert!(successes > 100);
}

#[test]
fn actual_selected_tile_plan_and_public_owner_boundary_bind_every_field_and_first_error() {
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(2)
            .unwrap()
            .with_maximum_work_units(1)
            .unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        for tile_scope in [false, true] {
            let (styles, quantizations, roi) = planning_fixture_owners(&layout, tile_scope);
            for tile in [0, 1, u16::MAX] {
                for discard in [0, 1, 2, 3, u8::MAX] {
                    for policy in [
                        (false, 0, false),
                        (false, 74, false),
                        (true, 1, true),
                        (true, 75, true),
                    ] {
                        for limit in &limits {
                            let expected = reference_tile_plan(
                                &layout.info.image_size,
                                layout.info.coding_style,
                                styles,
                                quantizations,
                                roi,
                                (tile, discard),
                                policy,
                                limit,
                            );
                            let actual = plan_progression_tile_at_selected(
                                &layout.info.image_size,
                                tile,
                                layout.info.coding_style,
                                styles,
                                quantizations,
                                roi,
                                discard,
                                policy.0,
                                policy.1,
                                policy.2,
                                limit,
                            );
                            successes += usize::from(assert_tile_plans_equal(actual, expected));
                            if discard == 0 && policy == (false, 74, false) {
                                let public = plan_progression_tile_at_with_component_overrides(
                                    &layout.info.image_size,
                                    tile,
                                    layout.info.coding_style,
                                    styles,
                                    quantizations,
                                    roi,
                                    limit,
                                );
                                assert_tile_plans_equal(
                                    public,
                                    reference_tile_plan(
                                        &layout.info.image_size,
                                        layout.info.coding_style,
                                        styles,
                                        quantizations,
                                        roi,
                                        (tile, discard),
                                        policy,
                                        limit,
                                    ),
                                );
                            }
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_440);
    assert!(successes > 10);
}

#[allow(clippy::too_many_arguments)]
fn reference_packet_reconstruction(
    mut plan: ProgressionTilePlan,
    parts: &[TilePartPayload<'_>],
    first: &TilePartPayload<'_>,
    size: &ImageSize,
    standard: (bool, bool),
    counts: Option<&[u8]>,
    limits: &ResourceLimits,
    mut prepared: Vec<PreparedTileComponent>,
    mut work: u64,
) -> Result<DecodedTileComponents, DecodeError> {
    let (grid, precincts) = plan.packet_execution();
    match counts {
        None => crate::packet::decode_progression_tile_packets(parts, grid, precincts, limits),
        Some(counts) => crate::packet::decode_progression_tile_packets_selected(
            parts,
            grid,
            precincts,
            Some(counts),
            limits,
        ),
    }?;
    reconstruct_planned_tile(
        &plan,
        first,
        size,
        standard,
        limits,
        &mut prepared,
        &mut work,
    )?;
    Ok(DecodedTileComponents {
        prepared,
        mct_work: work,
    })
}

#[test]
fn actual_packet_reconstruction_uses_real_bytes_complete_decoder_planes_and_owned_prepared_prefixes()
 {
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
        add_single_component_mct(prepared_codestream(1, 1, 1, &qcd, &[0, 0, 0]), 2, 3),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_packet_header_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_block_bytes(0)
            .unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    let mut nonzero = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        let first = &layout.tile_parts[0];
        let masks = [
            None,
            Some(Vec::new()),
            Some(vec![0; usize::from(layout.info.image_size.components)]),
            Some(vec![1; usize::from(layout.info.image_size.components)]),
            Some(vec![
                u8::MAX;
                usize::from(layout.info.image_size.components)
            ]),
        ];
        for tile_scope in [false, true] {
            let (styles, quantizations, roi) = planning_fixture_owners(&layout, tile_scope);
            let plan = || {
                plan_progression_tile_at_selected(
                    &layout.info.image_size,
                    0,
                    first.coding_style,
                    styles,
                    quantizations,
                    roi,
                    0,
                    false,
                    74,
                    false,
                    &ResourceLimits::HARDENED,
                )
                .unwrap()
            };
            for mask in &masks {
                for standard in [(false, false), (false, true), (true, false), (true, true)] {
                    for limit in &limits {
                        for work in [0, 1, u64::MAX] {
                            for prefix in [false, true] {
                                let prepared = || {
                                    if prefix {
                                        vec![PreparedTileComponent {
                                            component: u16::MAX,
                                            x: u32::MAX,
                                            y: 17,
                                            width: 1,
                                            height: 1,
                                            fraction_bits: u8::MAX,
                                            samples: vec![i64::MIN, i64::MAX],
                                        }]
                                    } else {
                                        Vec::new()
                                    }
                                };
                                for parts in [
                                    &layout.tile_parts[..],
                                    &layout.tile_parts[..0],
                                    &layout.tile_parts[..1],
                                ] {
                                    let expected = reference_packet_reconstruction(
                                        plan(),
                                        parts,
                                        first,
                                        &layout.info.image_size,
                                        standard,
                                        mask.as_deref(),
                                        limit,
                                        prepared(),
                                        work,
                                    );
                                    let actual = decode_planned_tile_components(
                                        plan(),
                                        parts,
                                        first,
                                        &layout.info.image_size,
                                        standard,
                                        mask.as_deref(),
                                        limit,
                                        prepared(),
                                        work,
                                    );
                                    match (actual, expected) {
                                        (Err(actual), Err(expected)) => {
                                            assert_eq!(actual, expected)
                                        }
                                        (Ok(actual), Ok(expected)) => {
                                            assert_eq!(actual.prepared, expected.prepared);
                                            assert_eq!(actual.mct_work, expected.mct_work);
                                            successes += 1;
                                            nonzero += usize::from(
                                                actual
                                                    .prepared
                                                    .iter()
                                                    .skip(usize::from(prefix))
                                                    .any(|component| {
                                                        component
                                                            .samples
                                                            .iter()
                                                            .any(|sample| *sample != 0)
                                                    }),
                                            );
                                        }
                                        (Err(error), Ok(_)) => panic!(
                                            "unexpected packet-reconstruction error: {error:?}"
                                        ),
                                        (Ok(_), Err(error)) => panic!(
                                            "packet reconstruction should have failed: {error:?}"
                                        ),
                                    }
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 14_400);
    assert!(successes > 10 && nonzero > 0);
}

fn reference_selected_component_blocks(
    plan: &PlannedTileComponent,
    mut total: u64,
) -> Result<u64, DecodeError> {
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    for placement in &plan.placements {
        let band = plan.subbands.get(placement.subband_index).ok_or(invalid)?;
        if band.resolution <= plan.output_resolution {
            total = u64::try_from(u128::from(total) + 1).map_err(|_| arithmetic)?;
        }
    }
    Ok(total)
}

#[test]
fn actual_selected_component_accounting_preserves_raw_band_indices_resolution_and_overflow_order() {
    let mut cases = 0;
    for output in [0, 1, 2, u8::MAX] {
        for resolution in [0, 1, 2, 31, 32, u8::MAX] {
            for bands in 0..4 {
                let subbands = (0..bands)
                    .map(|index| {
                        let mut band =
                            raw_planned_subband(u32::MAX, u32::MAX, 0, SubbandOrientation::Hh);
                        band.resolution = resolution.wrapping_add(u8::try_from(index).unwrap());
                        band
                    })
                    .collect::<Vec<_>>();
                for count in 0..5 {
                    for seed in [0, 1, bands, usize::MAX] {
                        let plan = PlannedTileComponent {
                            component: u16::MAX,
                            x: u32::MAX,
                            y: 17,
                            width: 0,
                            height: u32::MAX,
                            output_resolution: output,
                            subbands: subbands.clone(),
                            placements: (0..count)
                                .map(|index| ProgressionCodeBlockPlacement {
                                    precinct_index: usize::MAX,
                                    decoder_index: usize::MAX,
                                    subband_index: if index == 0 { seed } else { usize::MAX },
                                    x: u32::MAX,
                                    y: u32::MAX,
                                })
                                .collect(),
                        };
                        for total in [
                            0,
                            1,
                            2,
                            ResourceLimits::HARDENED.maximum_code_blocks(),
                            u64::MAX - 1,
                            u64::MAX,
                        ] {
                            assert_eq!(
                                count_selected_component_blocks(&plan, total),
                                reference_selected_component_blocks(&plan, total)
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 11_520);
}

fn reference_plan_accounting(
    plan: &ProgressionTilePlan,
    counts: Option<&[u8]>,
    initial: (u64, u64, u64),
    limits: &ResourceLimits,
) -> Result<(u64, u64, u64), DecodeError> {
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let add = |a: u64, b: u64| u64::try_from(u128::from(a) + u128::from(b)).map_err(|_| arithmetic);
    let packets = match counts {
        None => plan.grid.packet_count(),
        Some(counts) => plan.grid.selected_packet_count(counts)?,
    };
    let total_packets = add(initial.0, packets)?;
    if total_packets > limits.maximum_packets() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            limit: limits.maximum_packets(),
            actual: total_packets,
        });
    }
    let precincts = if counts.is_some() {
        if plan.coding_style.layers == 0 {
            return Err(arithmetic);
        }
        packets / u64::from(plan.coding_style.layers)
    } else {
        plan.grid.total_precinct_count()?
    };
    let total_precincts = add(initial.1, precincts)?;
    if total_precincts > limits.maximum_precincts() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::Precincts,
            limit: limits.maximum_precincts(),
            actual: total_precincts,
        });
    }
    let mut blocks = initial.2;
    for component in &plan.components {
        if counts.is_some() {
            blocks = reference_selected_component_blocks(component, blocks)?;
        } else {
            blocks = add(blocks, u64::try_from(component.placements.len()).unwrap())?;
            if blocks > limits.maximum_code_blocks() {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::CodeBlocks,
                    limit: limits.maximum_code_blocks(),
                    actual: blocks,
                });
            }
        }
    }
    if counts.is_some() && blocks > limits.maximum_code_blocks() {
        return Err(DecodeError::LimitExceeded {
            resource: Resource::CodeBlocks,
            limit: limits.maximum_code_blocks(),
            actual: blocks,
        });
    }
    Ok((total_packets, total_precincts, blocks))
}

#[test]
fn actual_layout_accounting_preserves_full_selected_global_limits_empty_and_malformed_plan_policy()
{
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(1)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_packets(1)
            .unwrap()
            .with_maximum_code_blocks(1)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
    ];
    let prior = [
        (0, 0, 0),
        (1, 2, 3),
        (u64::MAX, 0, 0),
        (0, u64::MAX, 0),
        (0, 0, u64::MAX),
        (u64::MAX, u64::MAX, u64::MAX),
        (0, ResourceLimits::HARDENED.maximum_precincts(), 0),
    ];
    let mut cases = 0;
    let mut successes = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        for tile_scope in [false, true] {
            let (styles, quantizations, roi) = planning_fixture_owners(&layout, tile_scope);
            let masks = [
                None,
                Some(Vec::new()),
                Some(vec![0; usize::from(layout.info.image_size.components)]),
                Some(vec![1; usize::from(layout.info.image_size.components)]),
                Some(vec![
                    u8::MAX;
                    usize::from(layout.info.image_size.components)
                ]),
            ];
            for variant in 0..6 {
                let mut plan = plan_progression_tile_at_selected(
                    &layout.info.image_size,
                    0,
                    layout.info.coding_style,
                    styles,
                    quantizations,
                    roi,
                    0,
                    false,
                    74,
                    false,
                    &ResourceLimits::HARDENED,
                )
                .unwrap();
                match variant {
                    0 => {}
                    1 => plan.components.clear(),
                    2 => plan.components[0].subbands.clear(),
                    3 => {
                        if let Some(placement) = plan.components[0].placements.last_mut() {
                            placement.subband_index = usize::MAX;
                        }
                    }
                    4 => plan.coding_style.layers = 0,
                    _ => plan.components[0].output_resolution = 0,
                }
                for counts in &masks {
                    for initial in prior {
                        for limit in &limits {
                            let expected =
                                reference_plan_accounting(&plan, counts.as_deref(), initial, limit);
                            assert_eq!(
                                account_planned_tile(&plan, counts.as_deref(), initial, limit),
                                expected
                            );
                            successes += usize::from(expected.is_ok());
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 7_560);
    assert!(successes > 100);
}

#[allow(clippy::too_many_arguments)]
fn reference_raw_tile_decode(
    size: &ImageSize,
    tile: u16,
    parts: &[TilePartPayload<'_>],
    profile: &codestream::CodestreamProfile,
    discard: Option<u8>,
    limits: &ResourceLimits,
    prepared: Vec<PreparedTileComponent>,
    initial: (u64, u64, u64),
    work: u64,
) -> Result<DecodedLayoutTile, DecodeError> {
    let metadata = prepare_tile_decode_metadata(parts, size.components, discard)?;
    let first = metadata.first;
    let counts = discard.map(|_| metadata.resolution_counts.as_slice());
    let policy = (
        profile.part15_allows_multiple_ht_sets(),
        profile.part15_magnitude_bound(),
        profile.part15_requires_all_ht_blocks(),
    );
    let plan = reference_tile_plan(
        size,
        first.coding_style,
        &first.component_coding_styles,
        &first.component_quantizations,
        &first.roi_shifts,
        (tile, discard.unwrap_or(0)),
        policy,
        limits,
    )?;
    let counters = reference_plan_accounting(&plan, counts, initial, limits)?;
    let decoded = reference_packet_reconstruction(
        plan,
        parts,
        first,
        size,
        metadata.standard,
        counts,
        limits,
        prepared,
        work,
    )?;
    Ok(DecodedLayoutTile {
        prepared: decoded.prepared,
        counters,
        mct_work: decoded.mct_work,
    })
}

#[test]
fn actual_raw_tile_decode_derives_all_samples_counters_work_and_first_errors_without_plan_results()
{
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
        add_single_component_mct(prepared_codestream(1, 1, 1, &qcd, &[0, 0, 0]), 2, 3),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_packet_header_bytes(0)
            .unwrap(),
    ];
    let prior = [
        (0, 0, 0),
        (1, 2, 3),
        (u64::MAX, 0, 0),
        (0, u64::MAX, 0),
        (0, 0, u64::MAX),
        (u64::MAX, u64::MAX, u64::MAX),
    ];
    let mut cases = 0;
    let mut successes = 0;
    let mut nonzero = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        for tile in [0, 1, u16::MAX] {
            for discard in [None, Some(0), Some(1), Some(2), Some(u8::MAX)] {
                for limit in &limits {
                    for initial in prior {
                        for work in [0, 1, u64::MAX] {
                            for prefix in [false, true] {
                                let prepared = || {
                                    if prefix {
                                        vec![PreparedTileComponent {
                                            component: u16::MAX,
                                            x: u32::MAX,
                                            y: 17,
                                            width: 1,
                                            height: 1,
                                            fraction_bits: u8::MAX,
                                            samples: vec![i64::MIN, i64::MAX],
                                        }]
                                    } else {
                                        Vec::new()
                                    }
                                };
                                for parts in [
                                    &layout.tile_parts[..],
                                    &layout.tile_parts[..0],
                                    &layout.tile_parts[..1],
                                ] {
                                    let expected = reference_raw_tile_decode(
                                        &layout.info.image_size,
                                        tile,
                                        parts,
                                        &layout.info.profile,
                                        discard,
                                        limit,
                                        prepared(),
                                        initial,
                                        work,
                                    );
                                    let actual = decode_tile_parts_at(
                                        &layout.info.image_size,
                                        tile,
                                        parts,
                                        &layout.info.profile,
                                        discard,
                                        limit,
                                        prepared(),
                                        initial,
                                        work,
                                    );
                                    match (actual, expected) {
                                        (Err(actual), Err(expected)) => {
                                            assert_eq!(actual, expected)
                                        }
                                        (Ok(actual), Ok(expected)) => {
                                            assert_eq!(actual.prepared, expected.prepared);
                                            assert_eq!(actual.counters, expected.counters);
                                            assert_eq!(actual.mct_work, expected.mct_work);
                                            successes += 1;
                                            nonzero += usize::from(
                                                actual
                                                    .prepared
                                                    .iter()
                                                    .skip(usize::from(prefix))
                                                    .any(|component| {
                                                        component
                                                            .samples
                                                            .iter()
                                                            .any(|sample| *sample != 0)
                                                    }),
                                            );
                                        }
                                        (Err(error), Ok(_)) => {
                                            panic!("unexpected raw-tile decode error: {error:?}")
                                        }
                                        (Ok(_), Err(error)) => {
                                            panic!("raw-tile decode should have failed: {error:?}")
                                        }
                                    }
                                    cases += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 38_880);
    assert!(successes > 10 && nonzero > 0);
}

#[test]
fn actual_codec_output_is_identical_for_source_parts_and_independent_complete_owned_copies() {
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        component_override_codestream(),
        add_single_component_mct(prepared_codestream(1, 1, 1, &qcd, &[0, 0, 0]), 2, 3),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ];
    let mut cases = 0;
    let mut successes = 0;
    let mut nonzero = 0;
    for bytes in fixtures {
        let layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
        let copied = collect_tile_parts(&layout.tile_parts, 0).unwrap();
        assert_eq!(copied, layout.tile_parts);
        for discard in [None, Some(0), Some(1), Some(2), Some(u8::MAX)] {
            for limit in &limits {
                for initial in [(0, 0, 0), (1, 2, 3), (u64::MAX, 0, 0), (0, 0, u64::MAX)] {
                    for work in [0, 1, u64::MAX] {
                        for prefix in [false, true] {
                            let prepared = || {
                                if prefix {
                                    vec![PreparedTileComponent {
                                        component: u16::MAX,
                                        x: u32::MAX,
                                        y: 17,
                                        width: 1,
                                        height: 1,
                                        fraction_bits: u8::MAX,
                                        samples: vec![i64::MIN, i64::MAX],
                                    }]
                                } else {
                                    Vec::new()
                                }
                            };
                            let source = decode_tile_parts_at(
                                &layout.info.image_size,
                                0,
                                &layout.tile_parts,
                                &layout.info.profile,
                                discard,
                                limit,
                                prepared(),
                                initial,
                                work,
                            );
                            let cloned = decode_tile_parts_at(
                                &layout.info.image_size,
                                0,
                                &copied,
                                &layout.info.profile,
                                discard,
                                limit,
                                prepared(),
                                initial,
                                work,
                            );
                            match (source, cloned) {
                                (Err(source), Err(cloned)) => assert_eq!(source, cloned),
                                (Ok(source), Ok(cloned)) => {
                                    assert_eq!(source.prepared, cloned.prepared);
                                    assert_eq!(source.counters, cloned.counters);
                                    assert_eq!(source.mct_work, cloned.mct_work);
                                    successes += 1;
                                    nonzero += usize::from(
                                        source.prepared.iter().skip(usize::from(prefix)).any(
                                            |component| {
                                                component.samples.iter().any(|sample| *sample != 0)
                                            },
                                        ),
                                    );
                                }
                                (Err(error), Ok(_)) | (Ok(_), Err(error)) => {
                                    panic!("copy changed codec outcome: {error:?}")
                                }
                            }
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 1_440);
    assert!(successes > 10 && nonzero > 0);
}

fn reference_complete_layout(
    layout: &CodestreamLayout<'_>,
    requested: Option<&DecodeSelection>,
    limits: &ResourceLimits,
) -> Result<DecodedImage, DecodeError> {
    validate_part2_execution(layout)?;
    let (tiles, selection) = match requested {
        None => {
            let count = layout.info.image_size.tile_count()?;
            if count > u64::from(u16::MAX) + 1 {
                return Err(DecodeError::MalformedInput {
                    offset: 0,
                    kind: MalformedKind::InvalidImageGeometry,
                });
            }
            (
                (0..count)
                    .map(|index| u16::try_from(index).unwrap())
                    .collect::<Vec<_>>(),
                None,
            )
        }
        Some(requested) => {
            let selection = validate_selection(&layout.info.image_size, requested)?;
            (
                selection.tiles,
                Some((selection.region, selection.discard_levels)),
            )
        }
    };
    let mut prepared = Vec::new();
    let mut counters = (0, 0, 0);
    let mut work = 0;
    for tile in tiles {
        let parts = layout
            .tile_parts
            .iter()
            .filter(|part| part.tile_index == tile)
            .cloned()
            .collect::<Vec<_>>();
        let decoded = reference_raw_tile_decode(
            &layout.info.image_size,
            tile,
            &parts,
            &layout.info.profile,
            selection.map(|value| value.1),
            limits,
            prepared,
            counters,
            work,
        )?;
        prepared = decoded.prepared;
        counters = decoded.counters;
        work = decoded.mct_work;
    }
    assemble_prepared_components(&layout.info.image_size, &prepared, selection, limits)
}

#[test]
fn actual_full_and_selected_layout_decode_derive_complete_images_from_real_source_parts_and_empty_state()
 {
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
        add_single_component_mct(prepared_codestream(1, 1, 1, &qcd, &[0, 0, 0]), 2, 3),
    ];
    let requests = [
        DecodeSelection::full_image(),
        DecodeSelection::full_image().with_discard_levels(1),
        DecodeSelection::full_image().with_discard_levels(2),
        DecodeSelection::full_image().with_discard_levels(u8::MAX),
        DecodeSelection::tile(0),
        DecodeSelection::tile(1),
        DecodeSelection::tile(u16::MAX),
        DecodeSelection::tiles(Vec::new()),
        DecodeSelection::tiles(vec![0, 1]),
        DecodeSelection::tiles(vec![1, 0]),
        DecodeSelection::tiles(vec![0, 0]),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(1, 0, 1, 1)),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(0, 0, 0, 0)),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(u32::MAX, 0, 2, 1)),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
    ];
    let mut full_cases = 0;
    let mut selected_cases = 0;
    let mut successes = 0;
    for bytes in fixtures {
        for variant in 0..9 {
            let mut layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
            match variant {
                0 => {}
                1 => layout.tile_parts.clear(),
                2 => layout.tile_parts.reverse(),
                3 => {
                    let duplicate = layout.tile_parts[0].clone();
                    layout.tile_parts.push(duplicate);
                }
                4 => layout.info.image_size.tiles_across = 0,
                5 => layout.info.image_size.tile_width = 0,
                6 => {
                    layout.info.image_size.tiles_across = 65_537;
                    layout.info.image_size.tiles_down = 1;
                }
                7 => layout.info.image_size.components = 0,
                _ => {
                    layout.info.image_size.width = u32::MAX;
                    layout.info.image_size.x_origin = 1;
                }
            }
            for limit in &limits {
                let expected = reference_complete_layout(&layout, None, limit);
                assert_eq!(decode_layout(&layout, limit), expected);
                successes += usize::from(expected.is_ok());
                full_cases += 1;
                for requested in &requests {
                    let expected = reference_complete_layout(&layout, Some(requested), limit);
                    assert_eq!(decode_layout_selected(&layout, requested, limit), expected);
                    successes += usize::from(expected.is_ok());
                    selected_cases += 1;
                }
            }
        }
    }
    assert_eq!(full_cases, 180);
    assert_eq!(selected_cases, 2_520);
    assert!(successes > 10);
}

#[test]
fn actual_full_selected_typed_layouts_join_real_decode_nonlinear_and_shape_producers() {
    use crate::codestream::{NonlinearPointTransform, Part2Extensions};

    fn reference(
        input_bytes: usize,
        layout: &CodestreamLayout<'_>,
        requested: Option<&DecodeSelection>,
        limits: &ResourceLimits,
    ) -> Result<TypedImage, DecodeError> {
        let decoded = reference_complete_layout(layout, requested, limits)?;
        let mut image = decoded.typed(limits)?;
        let discard_levels = requested.map_or(0, DecodeSelection::discard_levels);
        let regions = collect_nonlinear_regions(layout, &image, discard_levels)?;
        if !regions.is_empty() {
            image.apply_nonlinear_regions(&regions, limits)?;
        }
        let valid = input_bytes > 0
            && !layout.tile_parts.is_empty()
            && layout.info.image_size.components > 0
            && usize::from(layout.info.image_size.components) == image.components().len()
            && image.width() > 0
            && image.height() > 0
            && image.components().iter().all(|component| {
                let count = match component.samples() {
                    TypedSamples::Signed(values) => values.len(),
                    TypedSamples::Unsigned(values) => values.len(),
                };
                component.width() > 0
                    && component.height() > 0
                    && count as u128
                        == u128::from(component.width()) * u128::from(component.height())
            });
        if valid {
            Ok(image)
        } else {
            Err(invalid_decode())
        }
    }

    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let fixtures = [
        prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]),
        two_tile_codestream(),
        component_override_codestream(),
        add_single_component_mct(prepared_codestream(1, 1, 1, &qcd, &[0, 0, 0]), 2, 3),
    ];
    let requests = [
        DecodeSelection::full_image(),
        DecodeSelection::tile(0),
        DecodeSelection::tile(1),
        DecodeSelection::full_image().with_discard_levels(1),
        DecodeSelection::full_image().with_discard_levels(u8::MAX),
        DecodeSelection::full_image().with_region(crate::ImageRegion::new(0, 0, 1, 1)),
        DecodeSelection::tiles(Vec::new()),
    ];
    let limits = [
        ResourceLimits::HARDENED,
        ResourceLimits::HARDENED.with_maximum_work_units(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_decoded_bytes(0)
            .unwrap(),
        ResourceLimits::HARDENED.with_maximum_packets(0).unwrap(),
        ResourceLimits::HARDENED
            .with_maximum_code_blocks(0)
            .unwrap(),
    ];
    let one = 1_u32 << 16;
    let mut cases = 0;
    let mut successes = 0;
    let mut public_cases = 0;
    for bytes in fixtures {
        for variant in 0..10 {
            let mut layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
            match variant {
                0 => {}
                1 => layout.tile_parts.clear(),
                2 => layout.info.image_size.tiles_across = 0,
                3 => layout.info.image_size.components = 0,
                4..=7 => {
                    let transform = match variant {
                        5 => NonlinearPointTransform::for_test(
                            8,
                            false,
                            2,
                            Some(0),
                            Some(u32::MAX),
                            vec![0, 128, 255],
                        ),
                        6 => NonlinearPointTransform::for_test(0, false, 0, None, None, vec![]),
                        _ => NonlinearPointTransform::gamma_for_test(
                            8,
                            false,
                            [one, one, one, one, 0],
                        ),
                    };
                    layout.info.part2_extensions =
                        Part2Extensions::with_nonlinear_transform_for_test(transform);
                    for part in &mut layout.tile_parts {
                        part.part2_extensions = if variant == 7 {
                            Part2Extensions::default()
                        } else {
                            layout.info.part2_extensions.clone()
                        };
                    }
                }
                8 => {
                    layout.info.image_size.width = u32::MAX;
                    layout.info.image_size.x_origin = 1;
                }
                _ => {
                    for info in &mut layout.info.image_size.component_info {
                        info.signed = true;
                    }
                    let extensions = Part2Extensions::with_nonlinear_transform_for_test(
                        NonlinearPointTransform::for_test(8, true, 3, None, None, vec![]),
                    );
                    layout.info.part2_extensions = extensions.clone();
                    for part in &mut layout.tile_parts {
                        part.part2_extensions = extensions.clone();
                    }
                }
            }
            for limit in &limits {
                for input_bytes in [0, bytes.len(), usize::MAX] {
                    for requested in core::iter::once(None).chain(requests.iter().map(Some)) {
                        let expected = reference(input_bytes, &layout, requested, limit);
                        assert_eq!(
                            decode_typed_layout(input_bytes, &layout, limit, requested),
                            expected
                        );
                        successes += usize::from(expected.is_ok());
                        cases += 1;
                        if variant == 0 && input_bytes == bytes.len() {
                            let options = DecodeOptions::new(*limit);
                            let public = match requested {
                                None => decode_codestream(&bytes, &options),
                                Some(requested) => {
                                    decode_codestream_selected(&bytes, &options, requested)
                                }
                            };
                            let expected_public = parse_layout(&bytes, limit).and_then(|parsed| {
                                reference(bytes.len(), &parsed, requested, limit)
                            });
                            assert_eq!(public, expected_public);
                            public_cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 4_800);
    assert_eq!(public_cases, 160);
    assert!(successes > 10);
}

fn reference_standard_prepare(
    plan: &PlannedTileComponent,
    precincts: &[PacketPrecinctDecoder],
    style: CodingStyle,
    maximum: u64,
) -> Result<PreparedTileComponent, DecodeError> {
    use codestream::DecompositionDirection::{Horizontal, None, TwoDimensional, Vertical};
    let invalid = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let arithmetic = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::ArithmeticOverflow,
    };
    let invalid_style = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodingStyle,
    };
    if plan.subbands.is_empty() {
        return Err(invalid);
    }
    let reversible = match style.transform {
        WaveletTransform::Reversible5x3 => true,
        WaveletTransform::Irreversible9x7 => false,
        WaveletTransform::Arbitrary(_) => return Err(invalid),
    };
    if plan.output_resolution > style.decomposition_levels {
        return Err(invalid_style);
    }
    let mut directions = Vec::new();
    for resolution in 1..=u16::from(plan.output_resolution) {
        let stage = usize::from(style.decomposition_levels) - usize::from(resolution);
        directions.push(
            *style
                .decomposition_directions
                .get(stage)
                .ok_or(invalid_style)?,
        );
        if resolution == 255 {
            return Err(arithmetic);
        }
    }
    let selected = 1 + directions
        .iter()
        .map(|d| match d {
            None => 0,
            Horizontal | Vertical => 1,
            TwoDimensional => 3,
        })
        .sum::<usize>();
    if selected > plan.subbands.len() {
        return Err(invalid);
    }
    let fraction = if reversible { 0 } else { 16 };
    let mut bytes = 0_u128;
    let mut bands = Vec::new();
    for geometry in &plan.subbands[..selected] {
        let count = u128::from(geometry.width) * u128::from(geometry.height);
        if count > usize::MAX as u128 {
            return Err(arithmetic);
        }
        bytes += count * 9;
        if bytes > u128::from(u64::MAX) {
            return Err(arithmetic);
        }
        if bytes > u128::from(maximum) {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::DecodedBytes,
                limit: maximum,
                actual: u64::try_from(bytes).unwrap(),
            });
        }
        bands.push(WorkingSubband {
            width: geometry.width,
            height: geometry.height,
            fraction_bits: fraction,
            samples: vec![0; usize::try_from(count).unwrap()],
            visited: vec![false; usize::try_from(count).unwrap()],
        });
    }
    for placement in &plan.placements {
        if placement.subband_index >= selected {
            continue;
        }
        let geometry = plan.subbands[placement.subband_index];
        let precinct = precincts.get(placement.precinct_index).ok_or(invalid)?;
        let decoder = precinct.decoders().get(placement.decoder_index).ok_or(
            DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidPacketHeader,
            },
        )?;
        let plane = decoder.plane();
        let x1 = u64::from(placement.x) + u64::from(plane.width());
        let y1 = u64::from(placement.y) + u64::from(plane.height());
        if x1 > u64::from(u32::MAX) {
            return Err(arithmetic);
        }
        if x1 > u64::from(geometry.width) {
            return Err(invalid);
        }
        if y1 > u64::from(u32::MAX) {
            return Err(arithmetic);
        }
        if y1 > u64::from(geometry.height) {
            return Err(invalid);
        }
        let mut coefficients = Vec::new();
        for y in 0..plane.height() {
            for x in 0..plane.width() {
                let coefficient = plane
                    .coefficients()
                    .get(usize::from(y) * usize::from(plane.width()) + usize::from(x))
                    .ok_or(invalid)?;
                let mut words = [0; 6];
                // Fixtures finish the one-bit legacy block: any midpoint is zero.
                if coefficient.significant {
                    words[0] = coefficient.magnitude;
                }
                coefficients.push((words, coefficient.significant && coefficient.negative));
            }
        }
        let quantized = crate::transform::tests::reference_reconstruction(
            &coefficients,
            geometry.quantization_step,
            geometry.dynamic_range,
            reversible,
            geometry.roi_shift,
            maximum,
        )?;
        if quantized.2 != fraction {
            return Err(invalid);
        }
        reference_quantized_block(
            &mut bands[placement.subband_index],
            &quantized.3,
            [u32::from(plane.width()), u32::from(plane.height())],
            [placement.x, placement.y],
        )?;
    }
    if bands.iter().any(|band| band.visited.iter().any(|v| !v)) {
        return Err(invalid);
    }
    let ll = bands.first().ok_or(invalid)?;
    let mut reconstructed = (ll.width, ll.height, fraction, ll.samples.clone());
    let mut first = 1;
    for direction in directions {
        if direction == None {
            continue;
        }
        let detail = bands.get(first).ok_or(invalid)?;
        if detail.fraction_bits != fraction {
            return Err(invalid);
        }
        let geometry = plan.subbands[first];
        let low = WaveletBand {
            width: reconstructed.0,
            height: reconstructed.1,
            samples: &reconstructed.3,
        };
        let high = WaveletBand {
            width: detail.width,
            height: detail.height,
            samples: &detail.samples,
        };
        reconstructed = match direction {
            Horizontal => {
                first += 1;
                crate::transform::tests::reference_horizontal(
                    low,
                    high,
                    geometry.resolution_width,
                    geometry.low_pass_first_x,
                    !reversible,
                    maximum,
                )?
            }
            Vertical => {
                first += 1;
                crate::transform::tests::reference_vertical(
                    low,
                    high,
                    geometry.resolution_height,
                    geometry.low_pass_first_y,
                    !reversible,
                    maximum,
                )?
            }
            TwoDimensional => {
                let lh = bands.get(first + 1).ok_or(invalid)?;
                let hh = bands.get(first + 2).ok_or(invalid)?;
                if lh.fraction_bits != fraction || hh.fraction_bits != fraction {
                    return Err(invalid);
                }
                first += 3;
                crate::transform::tests::reference_level(
                    WaveletLevel {
                        ll: low,
                        hl: high,
                        lh: WaveletBand {
                            width: lh.width,
                            height: lh.height,
                            samples: &lh.samples,
                        },
                        hh: WaveletBand {
                            width: hh.width,
                            height: hh.height,
                            samples: &hh.samples,
                        },
                        output_width: geometry.resolution_width,
                        output_height: geometry.resolution_height,
                        low_pass_first_x: geometry.low_pass_first_x,
                        low_pass_first_y: geometry.low_pass_first_y,
                    },
                    !reversible,
                    maximum,
                )?
            }
            None => unreachable!(),
        };
        if reconstructed.2 != fraction {
            return Err(invalid);
        }
    }
    if reconstructed.0 != plan.width || reconstructed.1 != plan.height {
        return Err(invalid);
    }
    let count = u128::from(plan.width) * u128::from(plan.height);
    if count > usize::MAX as u128 {
        return Err(arithmetic);
    }
    if reconstructed.3.len() as u128 != count {
        return Err(invalid);
    }
    Ok(PreparedTileComponent {
        component: plan.component,
        x: plan.x,
        y: plan.y,
        width: plan.width,
        height: plan.height,
        fraction_bits: fraction,
        samples: reconstructed.3,
    })
}

fn standard_prepare_fixture(
    pattern: &[codestream::DecompositionDirection],
    reversible: bool,
    parity: bool,
    seed: u8,
) -> (
    PlannedTileComponent,
    Vec<PacketPrecinctDecoder>,
    CodingStyle,
) {
    use codestream::DecompositionDirection::*;
    let mut width = 1;
    let mut height = 1;
    let mut subbands = vec![SubbandGeometry {
        resolution: 0,
        orientation: SubbandOrientation::Ll,
        x0: u32::MAX,
        y0: 17,
        width,
        height,
        resolution_width: width,
        resolution_height: height,
        quantization_index: u16::MAX,
        quantization_step: QuantizationStep {
            exponent: 8,
            mantissa: 137,
        },
        dynamic_range: 8,
        significant_bitplanes: 1,
        roi_shift: 0,
        low_pass_first_x: parity,
        low_pass_first_y: parity,
    }];
    for (index, direction) in pattern.iter().enumerate() {
        let columns = width;
        let rows = height;
        if matches!(direction, Horizontal | TwoDimensional) {
            width *= 2;
        }
        if matches!(direction, Vertical | TwoDimensional) {
            height *= 2;
        }
        let count = match direction {
            None => 0,
            Horizontal | Vertical => 1,
            TwoDimensional => 3,
        };
        for detail in 0..count {
            subbands.push(SubbandGeometry {
                resolution: u8::try_from(index + 1).unwrap(),
                orientation: [
                    SubbandOrientation::Hl,
                    SubbandOrientation::Lh,
                    SubbandOrientation::Hh,
                ][detail],
                width: columns,
                height: rows,
                resolution_width: width,
                resolution_height: height,
                ..subbands[0]
            });
        }
    }
    let limits = ResourceLimits::default();
    let mut decoders = Vec::new();
    for geometry in &subbands {
        let mut decoder = Tier1CodeBlockDecoder::new(
            u16::try_from(geometry.width).unwrap(),
            u16::try_from(geometry.height).unwrap(),
            1,
            geometry.orientation,
            Tier1CodingStyle::default(),
        )
        .unwrap();
        decoder.decode_segment(&[seed; 64], 1, &limits).unwrap();
        assert!(decoder.is_complete());
        assert!(
            decoder
                .plane()
                .coefficients()
                .iter()
                .all(|c| c.magnitude <= 1)
        );
        decoders.push(decoder);
    }
    let precinct = PacketPrecinctDecoder::new(
        crate::packet::PacketPrecinctGeometry {
            component: u16::MAX,
            resolution: 0,
            precinct: 0,
            code_blocks_across: u32::try_from(decoders.len()).unwrap(),
            code_blocks_down: 1,
            maximum_zero_bitplanes: 1,
        },
        Tier1CodingStyle::default(),
        decoders,
        &limits,
    )
    .unwrap();
    let mut placements: Vec<_> = (0..subbands.len())
        .map(|index| ProgressionCodeBlockPlacement {
            precinct_index: 0,
            decoder_index: index,
            subband_index: index,
            x: 0,
            y: 0,
        })
        .collect();
    placements.reverse();
    placements.push(ProgressionCodeBlockPlacement {
        precinct_index: usize::MAX,
        decoder_index: usize::MAX,
        subband_index: usize::MAX,
        x: u32::MAX,
        y: u32::MAX,
    });
    let mut directions = [None; 32];
    for (index, direction) in pattern.iter().rev().enumerate() {
        directions[index] = *direction;
    }
    let style = CodingStyle {
        progression_order: ProgressionOrder::Lrcp,
        layers: 0,
        multiple_component_transform: false,
        decomposition_levels: u8::try_from(pattern.len()).unwrap(),
        decomposition_structure: Option::None,
        decomposition_directions: directions,
        code_block_width: 0,
        code_block_height: 0,
        code_block_style: 0,
        transform: if reversible {
            WaveletTransform::Reversible5x3
        } else {
            WaveletTransform::Irreversible9x7
        },
        precincts_defined: false,
        sop_markers: false,
        eph_markers: false,
        precinct_exponents: [(0, 0); 33],
    };
    (
        PlannedTileComponent {
            component: u16::MAX,
            x: u32::MAX,
            y: 123,
            width,
            height,
            output_resolution: u8::try_from(pattern.len()).unwrap(),
            subbands,
            placements,
        },
        vec![precinct],
        style,
    )
}

#[test]
fn full_native_kernel_preparation_preserves_real_dispatch_and_lazy_validation() {
    use crate::codestream::{DecompositionDirection, KernelCoefficient};
    let limits = ResourceLimits::default();
    let invalid_block = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidCodeBlock,
    };
    let invalid_transform = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::InvalidTransform,
    };
    for pattern in [
        vec![],
        vec![DecompositionDirection::Horizontal],
        vec![DecompositionDirection::Vertical],
        vec![DecompositionDirection::TwoDimensional],
        vec![
            DecompositionDirection::Horizontal,
            DecompositionDirection::Vertical,
        ],
    ] {
        for parity in [false, true] {
            let (plan, _, mut style) = standard_prepare_fixture(&pattern, true, parity, 0);
            let decoders = plan
                .subbands
                .iter()
                .map(|band| {
                    Tier1CodeBlockDecoder::new(
                        u16::try_from(band.width).unwrap(),
                        u16::try_from(band.height).unwrap(),
                        1,
                        band.orientation,
                        Tier1CodingStyle::default(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let precincts = vec![
                PacketPrecinctDecoder::new(
                    crate::packet::PacketPrecinctGeometry {
                        component: u16::MAX,
                        resolution: 0,
                        precinct: 0,
                        code_blocks_across: u32::try_from(decoders.len()).unwrap(),
                        code_blocks_down: 1,
                        maximum_zero_bitplanes: 1,
                    },
                    Tier1CodingStyle::default(),
                    decoders,
                    &limits,
                )
                .unwrap(),
            ];
            for reversible in [false, true] {
                style.transform = WaveletTransform::Arbitrary(0);
                let kernel = ArbitraryKernel::for_test(
                    reversible,
                    0,
                    false,
                    false,
                    false,
                    Some(KernelCoefficient::for_test(1, u8::MAX)),
                    vec![],
                );
                let expected = PreparedTileComponent {
                    component: plan.component,
                    x: plan.x,
                    y: plan.y,
                    width: plan.width,
                    height: plan.height,
                    fraction_bits: if reversible { 0 } else { 16 },
                    samples: vec![0; (plan.width * plan.height) as usize],
                };
                assert_eq!(
                    prepare_tile_component_with_kernel(
                        &plan,
                        &precincts,
                        style,
                        Some(&kernel),
                        &limits
                    ),
                    Ok(expected)
                );
                assert_eq!(
                    prepare_tile_component_with_kernel(&plan, &precincts, style, None, &limits),
                    Err(invalid_block)
                );
                let opposite = if reversible {
                    WaveletTransform::Irreversible9x7
                } else {
                    WaveletTransform::Reversible5x3
                };
                style.transform = opposite;
                if !pattern.is_empty() {
                    assert_eq!(
                        prepare_tile_component_with_kernel(
                            &plan,
                            &precincts,
                            style,
                            Some(&kernel),
                            &limits
                        ),
                        Err(invalid_block),
                    );
                }
            }
            style.transform = WaveletTransform::Arbitrary(0);
            let missing =
                ArbitraryKernel::for_test(false, u8::MAX, false, false, false, None, vec![]);
            let result = prepare_tile_component_with_kernel(
                &plan,
                &precincts,
                style,
                Some(&missing),
                &limits,
            );
            if pattern.is_empty() {
                let prepared = result.unwrap();
                assert_eq!(prepared.fraction_bits, 16);
                assert_eq!(prepared.samples, vec![0]);
            } else {
                assert_eq!(result, Err(invalid_transform));
            }
            let tiny = limits.with_maximum_decoded_bytes(1).unwrap();
            assert_eq!(
                prepare_tile_component_with_kernel(&plan, &precincts, style, Some(&missing), &tiny),
                Err(DecodeError::LimitExceeded {
                    resource: Resource::DecodedBytes,
                    limit: 1,
                    actual: 9
                }),
            );
        }
    }
}

#[test]
fn complete_standard_prepare_matches_independent_wide_multilevel_reference() {
    use codestream::DecompositionDirection::*;
    let patterns: &[&[_]] = &[
        &[],
        &[Horizontal],
        &[Vertical],
        &[TwoDimensional],
        &[None, Horizontal],
        &[Horizontal, None, Vertical],
        &[TwoDimensional, TwoDimensional],
        &[Horizontal, Vertical, TwoDimensional],
    ];
    let limits = ResourceLimits::default();
    let mut nonzero = false;
    for pattern in patterns {
        for reversible in [false, true] {
            for parity in [false, true] {
                for seed in [0, 17, 64, 128, 160] {
                    let (plan, precincts, style) =
                        standard_prepare_fixture(pattern, reversible, parity, seed);
                    nonzero |= precincts[0]
                        .decoders()
                        .iter()
                        .any(|d| d.plane().coefficients().iter().any(|c| c.significant));
                    assert_eq!(
                        prepare_tile_component(&plan, &precincts, style, &limits),
                        reference_standard_prepare(
                            &plan,
                            &precincts,
                            style,
                            limits.maximum_decoded_bytes()
                        )
                    );
                }
            }
        }
    }
    assert!(nonzero);
}

#[test]
fn complete_coefficient_reconstruction_preserves_prefix_mct_and_error_frontiers() {
    use codestream::{
        MctArray, MctArrayKind, MctNumericFormat, MctStage, MultipleComponentTransform,
    };
    let bytes = prepared_codestream(
        1,
        1,
        1,
        &[0, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40, 0x40],
        &[0],
    );
    let parser_limits = ResourceLimits::default();
    let layout = parse_layout(&bytes, &parser_limits).unwrap();
    for reversible in [false, true] {
        for seed in [0, 17, 128, 160] {
            for with_mct in [false, true] {
                for bad_tail in [false, true] {
                    for maximum in [8, 9, 64] {
                        let limits = ResourceLimits::default()
                            .with_maximum_decoded_bytes(maximum)
                            .unwrap();
                        let (mut component, precincts, style) =
                            standard_prepare_fixture(&[], reversible, false, seed);
                        component.component = 0;
                        component.x = 0;
                        component.y = 0;
                        let reference =
                            reference_standard_prepare(&component, &precincts, style, maximum);
                        let mut expected = vec![PreparedTileComponent {
                            component: u16::MAX,
                            x: 9,
                            y: 9,
                            width: 1,
                            height: 1,
                            fraction_bits: u8::MAX,
                            samples: vec![123],
                        }];
                        let mut expected_work = 7;
                        let expected_result = match reference {
                            Err(error) => Err(error),
                            Ok(prepared) => {
                                expected.push(prepared);
                                if bad_tail {
                                    Err(DecodeError::MalformedInput {
                                        offset: 0,
                                        kind: MalformedKind::InvalidCodingStyle,
                                    })
                                } else if with_mct {
                                    expected_work += 2;
                                    if maximum < 16 {
                                        Err(DecodeError::LimitExceeded {
                                            resource: Resource::DecodedBytes,
                                            limit: maximum,
                                            actual: 16,
                                        })
                                    } else {
                                        for value in &mut expected[1].samples {
                                            *value = if reversible {
                                                *value * 2 + 1
                                            } else {
                                                i64::try_from(
                                                    i128::from(*value) * 2 * (1_i128 << 16)
                                                        + (1_i128 << 32),
                                                )
                                                .unwrap()
                                            };
                                        }
                                        expected[1].fraction_bits = if reversible { 0 } else { 32 };
                                        Ok(())
                                    }
                                } else {
                                    Ok(())
                                }
                            }
                        };
                        let mut first = layout.tile_parts[0].clone();
                        first.coding_style = style;
                        first.component_coding_styles =
                            ComponentCodingStyles::uniform(1, style).unwrap();
                        if with_mct {
                            let array = |values| {
                                MctArray::from_values(
                                    0,
                                    MctArrayKind::Offset,
                                    MctNumericFormat::Int16,
                                    0,
                                    values,
                                )
                            };
                            first.multiple_component_transform =
                                Some(MultipleComponentTransform::from_stages(vec![
                                    MctStage::from_collections(
                                        0,
                                        vec![codestream::MctCollection::from_arrays(
                                            reversible,
                                            vec![0],
                                            vec![0],
                                            array(vec![2]),
                                            Some(array(vec![1])),
                                        )],
                                    ),
                                ]));
                        }
                        let mut components = vec![component];
                        if bad_tail {
                            let mut bad = standard_prepare_fixture(&[], reversible, false, seed).0;
                            bad.component = 1;
                            components.push(bad);
                        }
                        let plan = ProgressionTilePlan {
                            tile_index: 0,
                            coding_style: style,
                            component_coding_styles: first.component_coding_styles,
                            grid: PacketGrid::new(1, 1, 1, vec![1], &ResourceLimits::default())
                                .unwrap(),
                            precincts,
                            components,
                        };
                        let mut prepared = vec![PreparedTileComponent {
                            component: u16::MAX,
                            x: 9,
                            y: 9,
                            width: 1,
                            height: 1,
                            fraction_bits: u8::MAX,
                            samples: vec![123],
                        }];
                        let mut work = 7;
                        assert_eq!(
                            reconstruct_planned_tile(
                                &plan,
                                &first,
                                &layout.info.image_size,
                                (false, false),
                                &limits,
                                &mut prepared,
                                &mut work
                            ),
                            expected_result
                        );
                        assert_eq!(work, expected_work);
                        assert_eq!(prepared, expected);
                        if expected_result.is_ok() {
                            let assembled = assemble_prepared_components(
                                &layout.info.image_size,
                                &prepared[1..],
                                None,
                                &limits,
                            )
                            .unwrap();
                            assert_eq!(
                                assembled.component(0).unwrap().samples(),
                                expected[1].samples
                            );
                            assert_eq!(
                                assembled.component(0).unwrap().fraction_bits(),
                                expected[1].fraction_bits
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn complete_standard_prepare_preserves_all_ordered_rejections() {
    for variant in 0..15 {
        for maximum in [1, 8, 9, 17, 18, 35, 36, 1024] {
            let (mut plan, precincts, mut style) = standard_prepare_fixture(
                &[codestream::DecompositionDirection::TwoDimensional],
                true,
                true,
                17,
            );
            match variant {
                0 => plan.subbands.clear(),
                1 => style.transform = WaveletTransform::Arbitrary(255),
                2 => plan.output_resolution = 2,
                3 => style.decomposition_levels = 255,
                4 => {
                    plan.subbands.pop();
                }
                5 => plan.subbands[0].width = u32::MAX,
                6 => plan.subbands[0].dynamic_range = 0,
                7 => plan.subbands[0].quantization_step.mantissa = u16::MAX,
                8 => plan.placements[0].precinct_index = usize::MAX,
                9 => plan.placements[0].decoder_index = usize::MAX,
                10 => plan.placements[0].x = u32::MAX,
                11 => {
                    plan.placements.pop();
                    plan.placements.push(plan.placements[0]);
                }
                12 => plan.placements.clear(),
                13 => plan.width += 1,
                _ => plan.subbands[1].resolution_width = 0,
            }
            let limits = ResourceLimits::default()
                .with_maximum_decoded_bytes(maximum)
                .unwrap();
            assert_eq!(
                prepare_tile_component(&plan, &precincts, style, &limits),
                reference_standard_prepare(&plan, &precincts, style, maximum),
                "variant={variant} maximum={maximum}"
            );
        }
    }
}

fn copy_working_band(band: &WorkingSubband) -> WorkingSubband {
    WorkingSubband {
        width: band.width,
        height: band.height,
        fraction_bits: band.fraction_bits,
        samples: band.samples.clone(),
        visited: band.visited.clone(),
    }
}

fn observed_working_band(band: WorkingSubband) -> (u32, u32, u8, Vec<i64>, Vec<bool>) {
    (
        band.width,
        band.height,
        band.fraction_bits,
        band.samples,
        band.visited,
    )
}

fn reference_quantized_block(
    destination: &mut WorkingSubband,
    source: &[i64],
    block: [u32; 2],
    origin: [u32; 2],
) -> Result<(), DecodeError> {
    for y in 0..block[1] {
        for x in 0..block[0] {
            let destination_x = u64::from(origin[0]) + u64::from(x);
            let destination_y = u64::from(origin[1]) + u64::from(y);
            if destination_x > u64::from(u32::MAX) || destination_y > u64::from(u32::MAX) {
                return Err(arithmetic_overflow());
            }
            let output = u128::from(destination_y) * u128::from(destination.width)
                + u128::from(destination_x);
            if u128::from(destination_y) > usize::MAX as u128
                || u128::from(destination.width) > usize::MAX as u128
                || u128::from(destination_x) > usize::MAX as u128
                || output > usize::MAX as u128
            {
                return Err(arithmetic_overflow());
            }
            let input = u128::from(y) * u128::from(block[0]) + u128::from(x);
            if u128::from(y) > usize::MAX as u128
                || u128::from(block[0]) > usize::MAX as u128
                || u128::from(x) > usize::MAX as u128
                || input > usize::MAX as u128
            {
                return Err(arithmetic_overflow());
            }
            let output = output as usize;
            let input = input as usize;
            if output >= destination.samples.len()
                || output >= destination.visited.len()
                || input >= source.len()
                || destination.visited[output]
            {
                return Err(invalid_decode());
            }
            destination.samples[output] = source[input];
            destination.visited[output] = true;
        }
    }
    Ok(())
}

#[test]
fn complete_quantized_block_placement_matches_independent_wide_reference() {
    for width in 0..=5_u32 {
        for height in 0..=4_u32 {
            for block_width in 0..=4_u32 {
                for block_height in 0..=3_u32 {
                    let source: Vec<_> = (0..block_width * block_height + 1)
                        .map(|i| i64::from(i) * 13 - 29)
                        .collect();
                    for origin in [[0, 0], [1, 1], [width, height]] {
                        for source_count in [
                            (block_width * block_height) as usize,
                            (block_width * block_height).saturating_sub(1) as usize,
                            source.len(),
                        ] {
                            for previsited in [false, true] {
                                let mut actual = WorkingSubband {
                                    width,
                                    height,
                                    fraction_bits: 13,
                                    samples: vec![9; (width * height) as usize],
                                    visited: vec![false; (width * height) as usize],
                                };
                                if previsited && !actual.visited.is_empty() {
                                    let index = actual.visited.len() / 2;
                                    actual.visited[index] = true;
                                }
                                let mut expected = copy_working_band(&actual);
                                let expected_status = reference_quantized_block(
                                    &mut expected,
                                    &source[..source_count],
                                    [block_width, block_height],
                                    origin,
                                );
                                let status = write_quantized_block(
                                    &mut actual,
                                    &source[..source_count],
                                    block_width,
                                    block_height,
                                    origin[0],
                                    origin[1],
                                );
                                assert_eq!(
                                    (status, observed_working_band(actual)),
                                    (expected_status, observed_working_band(expected))
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn complete_quantized_block_failures_preserve_samples_visits_and_metadata() {
    for (band, source, block, origin) in [
        (
            WorkingSubband {
                width: 2,
                height: 3,
                fraction_bits: 16,
                samples: vec![9; 6],
                visited: vec![false; 6],
            },
            vec![i64::MIN, i64::MAX, 7, 8, 9],
            [2, 3],
            [0, 0],
        ),
        (
            WorkingSubband {
                width: 2,
                height: 123,
                fraction_bits: 0,
                samples: vec![9; 6],
                visited: vec![false; 3],
            },
            vec![1, 2, 3, 4, 5, 6],
            [2, 3],
            [0, 0],
        ),
        (
            WorkingSubband {
                width: 0,
                height: 0,
                fraction_bits: 255,
                samples: vec![9],
                visited: vec![false],
            },
            vec![7, 8],
            [1, 2],
            [0, u32::MAX],
        ),
        (
            WorkingSubband {
                width: 1,
                height: 1,
                fraction_bits: 7,
                samples: vec![9],
                visited: vec![true],
            },
            vec![],
            [1, 1],
            [0, 0],
        ),
        (
            WorkingSubband {
                width: u32::MAX,
                height: u32::MAX,
                fraction_bits: 0,
                samples: vec![],
                visited: vec![],
            },
            vec![1],
            [1, 1],
            [u32::MAX, u32::MAX],
        ),
        (
            WorkingSubband {
                width: 0,
                height: 0,
                fraction_bits: 19,
                samples: vec![],
                visited: vec![],
            },
            vec![],
            [0, 2],
            [u32::MAX, u32::MAX],
        ),
    ] {
        let mut actual = band;
        let mut expected = copy_working_band(&actual);
        let expected_status = reference_quantized_block(&mut expected, &source, block, origin);
        let status = write_quantized_block(
            &mut actual,
            &source,
            block[0],
            block[1],
            origin[0],
            origin[1],
        );
        assert_eq!(
            (status, observed_working_band(actual)),
            (expected_status, observed_working_band(expected))
        );
    }
}

#[test]
fn selected_color_bridge_composes_actual_conversion_crop_and_error_order() {
    use crate::codestream::ComponentInfo;
    use crate::color::{ConvertedChannelType, ConvertedColorSpace};
    use crate::image::{TypedComponent, TypedSamples};

    fn image(width: u32, height: u32, samples: Vec<u64>) -> TypedImage {
        TypedImage::from_components_with_origin(
            width,
            height,
            7,
            11,
            vec![TypedComponent::from_parts(
                width,
                height,
                ComponentInfo {
                    precision: 8,
                    signed: false,
                    x_subsampling: 1,
                    y_subsampling: 1,
                    x_registration: 0,
                    y_registration: 0,
                },
                TypedSamples::Unsigned(samples),
            )],
            &ResourceLimits::default(),
        )
        .unwrap()
    }
    let input = image(4, 2, vec![0, 32, 64, 96, 128, 160, 192, 255]);
    let gray = jp2::ColorSpecification::enumerated(jp2::ENUMERATED_GRAYSCALE);
    for (target, dimensions, expected) in [
        (
            [7, 11, 11, 13],
            (4, 2),
            vec![0, 8224, 16448, 24672, 32896, 41120, 49344, 65535],
        ),
        ([8, 11, 10, 13], (2, 2), vec![8224, 16448, 41120, 49344]),
        ([10, 12, 11, 13], (1, 1), vec![65535]),
    ] {
        let actual =
            convert_selected_color(&input, &gray, target, &ResourceLimits::default()).unwrap();
        assert_eq!((actual.width(), actual.height()), dimensions);
        assert_eq!(
            (actual.color_space(), actual.precision()),
            (ConvertedColorSpace::Grayscale, 16)
        );
        assert_eq!(actual.channels().len(), 1);
        assert_eq!(
            actual.channels()[0].channel_type(),
            ConvertedChannelType::Gray
        );
        assert_eq!(actual.channels()[0].samples(), expected);
    }
    for target in [
        [6, 11, 7, 12],
        [7, 10, 8, 11],
        [9, 11, 8, 12],
        [7, 12, 8, 11],
    ] {
        assert_eq!(
            convert_selected_color(&input, &gray, target, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::InvalidCodeBlock
            })
        );
    }
    for target in [[7, 11, 7, 12], [7, 11, 12, 13]] {
        assert_eq!(
            convert_selected_color(&input, &gray, target, &ResourceLimits::default()),
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ContainerCodestreamMismatch
            })
        );
    }
    let target = [6, 11, 7, 12];
    assert_eq!(
        convert_selected_color(
            &input,
            &jp2::ColorSpecification::enumerated(99),
            target,
            &ResourceLimits::default()
        ),
        Err(DecodeError::UnsupportedColorConversion {
            reason: crate::UnsupportedColorConversion::EnumeratedColorSpace
        })
    );
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(1)
        .unwrap();
    assert_eq!(
        convert_selected_color(&input, &gray, target, &limits),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 16
        })
    );
    assert_eq!(
        convert_selected_color(
            &image(1, 1, vec![256]),
            &gray,
            target,
            &ResourceLimits::default()
        ),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ContainerCodestreamMismatch
        })
    );
}

fn segment(marker: u16, payload: &[u8]) -> Vec<u8> {
    let length = u16::try_from(payload.len() + 2).unwrap();
    let mut bytes = marker.to_be_bytes().to_vec();
    bytes.extend_from_slice(&length.to_be_bytes());
    bytes.extend_from_slice(payload);
    bytes
}

fn prepared_codestream(
    width: u32,
    height: u32,
    transform: u8,
    qcd: &[u8],
    packet_bytes: &[u8],
) -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&width.to_be_bytes());
    siz.extend_from_slice(&height.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);
    let cod = [0, 0, 0, 1, 0, 2, 0, 0, 0, transform];
    let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
    bytes.extend(segment(0xff51, &siz));
    bytes.extend(segment(0xff52, &cod));
    bytes.extend(segment(0xff5c, qcd));
    let tile_start = bytes.len();
    let mut sot = Vec::new();
    sot.extend_from_slice(&0_u16.to_be_bytes());
    sot.extend_from_slice(&0_u32.to_be_bytes());
    sot.extend_from_slice(&[0, 1]);
    bytes.extend(segment(0xff90, &sot));
    bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
    bytes.extend_from_slice(packet_bytes);
    let tile_length = u32::try_from(bytes.len() - tile_start).unwrap();
    bytes[tile_start + 6..tile_start + 10].copy_from_slice(&tile_length.to_be_bytes());
    bytes.extend_from_slice(&0xffd9_u16.to_be_bytes());
    bytes
}

fn add_plt(mut bytes: Vec<u8>, lengths: &[u8]) -> Vec<u8> {
    assert!(lengths.iter().all(|length| *length > 0 && *length < 128));
    let sod = bytes
        .windows(2)
        .position(|window| window == 0xff93_u16.to_be_bytes())
        .unwrap();
    let mut payload = vec![0];
    payload.extend_from_slice(lengths);
    bytes.splice(sod..sod, segment(0xff58, &payload));
    let sot = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let eoc = bytes.len() - 2;
    let tile_length = u32::try_from(eoc - sot).unwrap();
    bytes[sot + 6..sot + 10].copy_from_slice(&tile_length.to_be_bytes());
    bytes
}

fn add_single_component_mct(mut bytes: Vec<u8>, matrix: i16, offset: i16) -> Vec<u8> {
    let sot = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let mut markers = Vec::new();
    let mut matrix_payload = 0_u16.to_be_bytes().to_vec();
    matrix_payload.extend_from_slice(&0x0101_u16.to_be_bytes());
    matrix_payload.extend_from_slice(&0_u16.to_be_bytes());
    matrix_payload.extend_from_slice(&matrix.to_be_bytes());
    markers.extend(segment(0xff74, &matrix_payload));
    let mut offset_payload = 0_u16.to_be_bytes().to_vec();
    offset_payload.extend_from_slice(&0x0202_u16.to_be_bytes());
    offset_payload.extend_from_slice(&0_u16.to_be_bytes());
    offset_payload.extend_from_slice(&offset.to_be_bytes());
    markers.extend(segment(0xff74, &offset_payload));
    markers.extend(segment(
        0xff75,
        &[0, 0, 7, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 2, 1],
    ));
    markers.extend(segment(0xff77, &[1, 7]));
    bytes.splice(sot..sot, markers);
    bytes
}

fn add_second_component_mct_stage(mut bytes: Vec<u8>, matrix: i16, offset: i16) -> Vec<u8> {
    let mco = bytes
        .windows(2)
        .position(|window| window == 0xff77_u16.to_be_bytes())
        .unwrap();
    let mut markers = Vec::new();
    let mut matrix_payload = 0_u16.to_be_bytes().to_vec();
    matrix_payload.extend_from_slice(&0x0103_u16.to_be_bytes());
    matrix_payload.extend_from_slice(&0_u16.to_be_bytes());
    matrix_payload.extend_from_slice(&matrix.to_be_bytes());
    markers.extend(segment(0xff74, &matrix_payload));
    let mut offset_payload = 0_u16.to_be_bytes().to_vec();
    offset_payload.extend_from_slice(&0x0204_u16.to_be_bytes());
    offset_payload.extend_from_slice(&0_u16.to_be_bytes());
    offset_payload.extend_from_slice(&offset.to_be_bytes());
    markers.extend(segment(0xff74, &offset_payload));
    markers.extend(segment(
        0xff75,
        &[0, 0, 8, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 4, 3],
    ));
    markers.extend(segment(0xff77, &[2, 7, 8]));
    bytes.splice(mco..mco + 6, markers);
    bytes
}

fn pack_packet_header(mut bytes: Vec<u8>, ppm: bool, header: &[u8]) -> Vec<u8> {
    let sod = bytes
        .windows(2)
        .position(|window| window == 0xff93_u16.to_be_bytes())
        .unwrap();
    bytes.drain(sod + 2..sod + 2 + header.len());
    if ppm {
        let sot = bytes
            .windows(2)
            .position(|window| window == 0xff90_u16.to_be_bytes())
            .unwrap();
        let mut payload = vec![0];
        payload.extend_from_slice(&u32::try_from(header.len()).unwrap().to_be_bytes());
        payload.extend_from_slice(header);
        bytes.splice(sot..sot, segment(0xff60, &payload));
    } else {
        let sod = bytes
            .windows(2)
            .position(|window| window == 0xff93_u16.to_be_bytes())
            .unwrap();
        let mut payload = vec![0];
        payload.extend_from_slice(header);
        bytes.splice(sod..sod, segment(0xff61, &payload));
    }
    let sot = bytes
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let eoc = bytes.len() - 2;
    let tile_length = u32::try_from(eoc - sot).unwrap();
    bytes[sot + 6..sot + 10].copy_from_slice(&tile_length.to_be_bytes());
    bytes
}

fn jp2_for_codestream(codestream: &[u8], width: u32, height: u32) -> Vec<u8> {
    let mut jp2 = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jp2.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jp2.extend(box32(*b"jp2h", &header));
    jp2.extend(box32(*b"jp2c", codestream));
    jp2
}

fn jpx_for_codestreams(codestreams: &[Vec<u8>], width: u32, height: u32) -> Vec<u8> {
    let mut jpx = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jpx.extend(box32(*b"ftyp", b"jpxb\0\0\0\0jpxb"));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jpx.extend(box32(*b"jp2h", &header));
    for codestream in codestreams {
        jpx.extend(box32(*b"jp2c", codestream));
    }
    jpx
}

fn jpx_for_compositing_layers(
    codestreams: &[Vec<u8>],
    width: u32,
    height: u32,
    with_instruction: bool,
) -> Vec<u8> {
    let mut jpx = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jpx.extend(box32(*b"ftyp", b"jpxb\0\0\0\0jpxb"));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&height.to_be_bytes());
    image_header.extend_from_slice(&width.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jpx.extend(box32(*b"jp2h", &header));
    for _ in codestreams {
        jpx.extend(box32(*b"jpch", &header));
    }
    for index in 0..codestreams.len() {
        let mut registration = 1_u16.to_be_bytes().to_vec();
        registration.extend_from_slice(&1_u16.to_be_bytes());
        registration.extend_from_slice(&u16::try_from(index).unwrap().to_be_bytes());
        registration.extend_from_slice(&[1, 1, 0, 0]);
        jpx.extend(box32(*b"jplh", &box32(*b"creg", &registration)));
    }
    let mut composition_options = height.to_be_bytes().to_vec();
    composition_options.extend_from_slice(
        &width
            .checked_mul(u32::try_from(codestreams.len()).unwrap())
            .unwrap()
            .to_be_bytes(),
    );
    composition_options.push(0);
    let mut composition = box32(*b"copt", &composition_options);
    if with_instruction {
        let mut instruction = 5_u16.to_be_bytes().to_vec();
        instruction.extend_from_slice(&0_u16.to_be_bytes());
        instruction.extend_from_slice(&1_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        instruction.extend_from_slice(&100_u32.to_be_bytes());
        instruction.extend_from_slice(&0_u32.to_be_bytes());
        composition.extend(box32(*b"inst", &instruction));
    }
    jpx.extend(box32(*b"comp", &composition));
    for codestream in codestreams {
        jpx.extend(box32(*b"jp2c", codestream));
    }
    jpx
}

fn jp2_with_palette(
    codestream: &[u8],
    palette_entries: u16,
    include_channel_definitions: bool,
) -> Vec<u8> {
    let mut jp2 = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jp2.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    let mut palette = palette_entries.to_be_bytes().to_vec();
    palette.extend_from_slice(&[2, 7, 0x84]);
    let mut entry = 0_u16;
    while entry < palette_entries {
        if entry == 128 {
            palette.extend_from_slice(&[42, 0x1d]);
        } else {
            palette.extend_from_slice(&[0, 0]);
        }
        entry += 1;
    }
    header.extend(box32(*b"pclr", &palette));
    header.extend(box32(*b"cmap", &[0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0]));
    if include_channel_definitions {
        let mut definitions = 3_u16.to_be_bytes().to_vec();
        definitions.extend_from_slice(&[0, 0, 0, 0, 0, 1]);
        definitions.extend_from_slice(&[0, 1, 0, 1, 0, 1]);
        definitions.extend_from_slice(&[0, 2, 0xff, 0xff, 0xff, 0xff]);
        header.extend(box32(*b"cdef", &definitions));
    }
    jp2.extend(box32(*b"jp2h", &header));
    jp2.extend(box32(*b"jp2c", codestream));
    jp2
}

#[test]
fn whole_output_header_matches_independent_native_order_and_admission_oracle() {
    use crate::codestream::ComponentInfo;
    use crate::image::{ChannelAssociation, ChannelDefinition, ChannelType};

    type OutputComponent = (
        u32,
        u32,
        ComponentInfo,
        TypedSamples,
        Vec<ChannelDefinition>,
    );
    type OutputImage = ((u32, u32, u32, u32), Vec<OutputComponent>);

    fn malformed(kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput { offset: 0, kind }
    }

    fn own_samples(samples: &TypedSamples) -> TypedSamples {
        match samples {
            TypedSamples::Signed(values) => TypedSamples::Signed(values.clone()),
            TypedSamples::Unsigned(values) => TypedSamples::Unsigned(values.clone()),
        }
    }

    fn observe(image: &TypedImage) -> OutputImage {
        (
            (
                image.width(),
                image.height(),
                image.x_origin(),
                image.y_origin(),
            ),
            image
                .components()
                .iter()
                .map(|component| {
                    (
                        component.width(),
                        component.height(),
                        component.info(),
                        own_samples(component.samples()),
                        component.channel_definitions().to_vec(),
                    )
                })
                .collect(),
        )
    }

    fn source(case: usize) -> TypedImage {
        let mut components = Vec::new();
        for index in 0..2 {
            let info = ComponentInfo {
                precision: 0,
                signed: index != 0,
                x_subsampling: 0,
                y_subsampling: u8::MAX,
                x_registration: u16::MAX,
                y_registration: 17,
            };
            let samples = match (case, index) {
                (3 | 6, _) => TypedSamples::Signed(vec![]),
                (4, 0) => TypedSamples::Unsigned(vec![u64::MAX]),
                (5, 0) => TypedSamples::Signed(vec![-1]),
                (_, 0) => TypedSamples::Signed(vec![0, 1]),
                (_, _) => TypedSamples::Unsigned(vec![1, 0]),
            };
            let (width, height) = match case {
                2 if index == 0 => (3, 1),
                3 => (0, u32::MAX),
                4 | 5 if index == 0 => (1, 1),
                6 => (u32::MAX, u32::MAX),
                _ => (2, 1),
            };
            let mut component = TypedComponent::from_parts(width, height, info, samples);
            component.add_channel_definition(ChannelDefinition::new(
                ChannelType::Unspecified,
                ChannelAssociation::Color(u16::MAX),
            ));
            components.push(component);
        }
        TypedImage::for_test(2, 1, if case == 1 { u32::MAX } else { 3 }, 5, components)
    }

    fn oracle(
        image: &TypedImage,
        mappings: &[jp2::ComponentMapping],
        definitions: &[jp2::ChannelDefinitionRecord],
        palette: bool,
        maximum: u64,
    ) -> Result<OutputImage, DecodeError> {
        let (geometry, input) = observe(image);
        let mut output = Vec::new();
        if mappings.is_empty() {
            output = input;
        } else {
            for mapping in mappings {
                let source = input
                    .get(usize::from(mapping.component))
                    .ok_or(malformed(MalformedKind::InvalidImageGeometry))?;
                let samples = match mapping.mapping_type {
                    jp2::MappingType::Direct => own_samples(&source.3),
                    jp2::MappingType::Palette { column } => {
                        if !palette || column != 0 {
                            return Err(malformed(MalformedKind::ContainerCodestreamMismatch));
                        }
                        let indices = match &source.3 {
                            TypedSamples::Signed(values) => values
                                .iter()
                                .map(|value| i128::from(*value))
                                .collect::<Vec<_>>(),
                            TypedSamples::Unsigned(values) => values
                                .iter()
                                .map(|value| i128::from(*value))
                                .collect::<Vec<_>>(),
                        };
                        let mut values = Vec::new();
                        for index in indices {
                            if !(0..2).contains(&index) {
                                return Err(malformed(MalformedKind::ContainerCodestreamMismatch));
                            }
                            values.push(if index == 0 { 7 } else { -3 });
                        }
                        TypedSamples::Signed(values)
                    }
                };
                let (info, definitions) = match mapping.mapping_type {
                    jp2::MappingType::Direct => (source.2, source.4.clone()),
                    jp2::MappingType::Palette { .. } => (
                        ComponentInfo {
                            precision: 8,
                            signed: true,
                            ..source.2
                        },
                        vec![],
                    ),
                };
                output.push((source.0, source.1, info, samples, definitions));
            }
        }
        for record in definitions {
            let component = output
                .get_mut(usize::from(record.channel))
                .ok_or(malformed(MalformedKind::ContainerCodestreamMismatch))?;
            component.4.push(record.definition);
        }
        if u64::from(geometry.0) + u64::from(geometry.2) > u64::from(u32::MAX)
            || u64::from(geometry.1) + u64::from(geometry.3) > u64::from(u32::MAX)
        {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        if output.len() > usize::from(u16::MAX) {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        if output.len() > 64 {
            return Err(DecodeError::LimitExceeded {
                resource: Resource::Components,
                limit: 64,
                actual: output.len() as u64,
            });
        }
        let mut bytes = 0_u128;
        for component in &output {
            let area = u128::from(component.0) * u128::from(component.1);
            if area > usize::MAX as u128 {
                return Err(malformed(MalformedKind::ArithmeticOverflow));
            }
            let length = match &component.3 {
                TypedSamples::Signed(values) => values.len(),
                TypedSamples::Unsigned(values) => values.len(),
            };
            if area != length as u128 {
                return Err(malformed(MalformedKind::InvalidImageGeometry));
            }
            bytes += length as u128 * 8;
            if bytes > u128::from(u64::MAX) {
                return Err(malformed(MalformedKind::ArithmeticOverflow));
            }
            if bytes > u128::from(maximum) {
                return Err(DecodeError::LimitExceeded {
                    resource: Resource::DecodedBytes,
                    limit: maximum,
                    actual: bytes as u64,
                });
            }
        }
        Ok((geometry, output))
    }

    let definition = ChannelDefinition::new(ChannelType::Opacity, ChannelAssociation::WholeImage);
    let record = |channel| jp2::ChannelDefinitionRecord {
        channel,
        definition,
    };
    let definitions = [
        vec![],
        vec![record(0)],
        vec![record(0), record(0)],
        vec![record(1), record(0)],
        vec![record(2)],
        vec![record(u16::MAX)],
    ];
    let choices = [
        jp2::ComponentMapping {
            component: 0,
            mapping_type: jp2::MappingType::Direct,
        },
        jp2::ComponentMapping {
            component: 1,
            mapping_type: jp2::MappingType::Direct,
        },
        jp2::ComponentMapping {
            component: 0,
            mapping_type: jp2::MappingType::Palette { column: 0 },
        },
        jp2::ComponentMapping {
            component: 0,
            mapping_type: jp2::MappingType::Palette { column: 1 },
        },
        jp2::ComponentMapping {
            component: u16::MAX,
            mapping_type: jp2::MappingType::Palette { column: 0 },
        },
    ];
    let mut mapping_cases = vec![vec![]];
    for first in choices {
        mapping_cases.push(vec![first]);
        for second in choices {
            mapping_cases.push(vec![first, second]);
        }
    }
    let mut contexts = 0;
    for mappings in mapping_cases {
        for palette in [false, true] {
            for records in &definitions {
                for case in 0..7 {
                    for maximum in [1, 15, 16, 31, 32, 48] {
                        let header = jp2::Jp2Header {
                            image: jp2::ImageHeader {
                                width: u32::MAX,
                                height: 0,
                                components: 0,
                                bit_depth: jp2::ComponentBitDepth::Variable,
                                unknown_color_space: true,
                                intellectual_property: true,
                            },
                            color: jp2::ColorSpecification::enumerated(u32::MAX),
                            nested_box_count: u32::MAX,
                            palette_entries: u16::MAX,
                            palette_columns: u8::MAX,
                            component_mapping_entries: u16::MAX,
                            channel_definitions: u16::MAX,
                            palette: palette.then(|| {
                                jp2::Palette::for_test(
                                    2,
                                    vec![jp2::PaletteColumn {
                                        precision: 8,
                                        signed: true,
                                    }],
                                    vec![7, -3],
                                )
                            }),
                            component_mappings: mappings.clone(),
                            channel_definition_records: records.clone(),
                            capture_resolution: None,
                            display_resolution: None,
                        };
                        let input = source(case);
                        let expected = oracle(&input, &mappings, records, palette, maximum);
                        let limits = ResourceLimits::default()
                            .with_maximum_decoded_bytes(maximum)
                            .unwrap();
                        let actual =
                            apply_jp2_output(input, &header, &limits).map(|image| observe(&image));
                        assert_eq!(
                            actual, expected,
                            "case={case} maximum={maximum} mappings={mappings:?} palette={palette} records={records:?}"
                        );
                        contexts += 1;
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 15_624);
}

#[test]
fn palette_component_mapping_matches_independent_complete_native_oracle() {
    use crate::codestream::ComponentInfo;
    use crate::image::{ChannelAssociation, ChannelDefinition, ChannelType};

    fn malformed(kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput { offset: 0, kind }
    }

    fn samples(case: usize) -> TypedSamples {
        match case {
            0 => TypedSamples::Signed(vec![]),
            1 => TypedSamples::Signed(vec![-1]),
            2 => TypedSamples::Signed(vec![0]),
            3 => TypedSamples::Signed(vec![1, 0]),
            4 => TypedSamples::Signed(vec![i64::from(u16::MAX)]),
            5 => TypedSamples::Signed(vec![i64::MIN]),
            6 => TypedSamples::Signed(vec![0, 2, 1]),
            7 => TypedSamples::Signed(vec![i64::MAX]),
            8 => TypedSamples::Unsigned(vec![]),
            9 => TypedSamples::Unsigned(vec![0]),
            10 => TypedSamples::Unsigned(vec![1, 0]),
            11 => TypedSamples::Unsigned(vec![u64::from(u16::MAX)]),
            12 => TypedSamples::Unsigned(vec![u64::MAX]),
            13 => TypedSamples::Unsigned(vec![0, 2, 1]),
            _ => unreachable!(),
        }
    }

    fn oracle(
        input: &TypedSamples,
        entries: u16,
        columns: &[jp2::PaletteColumn],
        values: &[i64],
        column: u8,
    ) -> Result<TypedSamples, DecodeError> {
        let descriptor = columns
            .get(usize::from(column))
            .ok_or(malformed(MalformedKind::ContainerCodestreamMismatch))?;
        if descriptor.precision == 0 || descriptor.precision > 38 {
            return Err(malformed(MalformedKind::ContainerCodestreamMismatch));
        }
        let input = match input {
            TypedSamples::Signed(values) => values
                .iter()
                .map(|value| i128::from(*value))
                .collect::<Vec<_>>(),
            TypedSamples::Unsigned(values) => values
                .iter()
                .map(|value| i128::from(*value))
                .collect::<Vec<_>>(),
        };
        let modulus = 2_i128.pow(u32::from(descriptor.precision));
        let (minimum, maximum) = if descriptor.signed {
            (-(modulus / 2), modulus / 2 - 1)
        } else {
            (0, modulus - 1)
        };
        let mut signed = Vec::new();
        let mut unsigned = Vec::new();
        for index in input {
            if index < 0 || index > i128::from(u16::MAX) || index >= i128::from(entries) {
                return Err(malformed(MalformedKind::ContainerCodestreamMismatch));
            }
            if columns.len() > usize::from(u8::MAX) {
                return Err(malformed(MalformedKind::ArithmeticOverflow));
            }
            let address = (index as u128) * columns.len() as u128 + u128::from(column);
            if address > usize::MAX as u128 {
                return Err(malformed(MalformedKind::ArithmeticOverflow));
            }
            let value = *values
                .get(address as usize)
                .ok_or(malformed(MalformedKind::InvalidBoxContents))?;
            if i128::from(value) < minimum || i128::from(value) > maximum {
                return Err(malformed(MalformedKind::ContainerCodestreamMismatch));
            }
            if descriptor.signed {
                signed.push(value);
            } else {
                unsigned.push(u64::try_from(value).unwrap());
            }
        }
        Ok(if descriptor.signed {
            TypedSamples::Signed(signed)
        } else {
            TypedSamples::Unsigned(unsigned)
        })
    }

    let tables = [
        vec![],
        vec![0, -1],
        vec![127, -128, 255, 0, i64::MIN, i64::MAX],
        vec![
            (1_i64 << 37) - 1,
            -(1_i64 << 37),
            (1_i64 << 38) - 1,
            1_i64 << 38,
        ],
    ];
    let mut contexts = 0;
    for entries in [0, 1, 2, u16::MAX] {
        for column_count in [0, 1, 2, 256] {
            for column in [0, 1, u8::MAX] {
                for precision in [0, 1, 8, 16, 38, 39, u8::MAX] {
                    for signed in [false, true] {
                        let columns = vec![jp2::PaletteColumn { precision, signed }; column_count];
                        for values in &tables {
                            let palette =
                                jp2::Palette::for_test(entries, columns.clone(), values.clone());
                            for case in 0..14 {
                                let info = ComponentInfo {
                                    precision: [0, 1, 38, u8::MAX][case % 4],
                                    signed: case % 2 == 0,
                                    x_subsampling: [0, 2, u8::MAX][case % 3],
                                    y_subsampling: [u8::MAX, 0, 1][case % 3],
                                    x_registration: u16::MAX,
                                    y_registration: case as u16,
                                };
                                let width = if case % 3 == 0 { 0 } else { 5 };
                                let height = if case % 5 == 0 { u32::MAX } else { 1 };
                                let mut source =
                                    TypedComponent::from_parts(width, height, info, samples(case));
                                source.add_channel_definition(ChannelDefinition::new(
                                    ChannelType::Unspecified,
                                    ChannelAssociation::Color(u16::MAX),
                                ));
                                source.add_channel_definition(ChannelDefinition::new(
                                    ChannelType::PremultipliedOpacity,
                                    ChannelAssociation::WholeImage,
                                ));
                                assert_eq!(copy_typed_component(&source).unwrap(), source);
                                let expected =
                                    oracle(source.samples(), entries, &columns, values, column);
                                match (expected, map_palette_component(&source, &palette, column)) {
                                    (Err(expected), Err(actual)) => {
                                        assert_eq!(actual, expected)
                                    }
                                    (Ok(expected), Ok(actual)) => {
                                        assert_eq!(actual.width(), width);
                                        assert_eq!(actual.height(), height);
                                        assert_eq!(
                                            actual.info(),
                                            ComponentInfo {
                                                precision,
                                                signed,
                                                ..info
                                            }
                                        );
                                        assert_eq!(actual.samples(), &expected);
                                        assert!(actual.channel_definitions().is_empty());
                                    }
                                    (expected, actual) => panic!(
                                        "entries={entries} columns={column_count} column={column} precision={precision} signed={signed} case={case}: expected={expected:?} actual={actual:?}"
                                    ),
                                }
                                assert_eq!(source.info(), info);
                                assert_eq!(source.channel_definitions().len(), 2);
                                contexts += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 37_632);
}

#[test]
fn palette_component_modulus_matches_all_native_precisions() {
    for precision in 0..=u8::MAX {
        let expected = if (1..=38).contains(&precision) {
            Ok((1_u128 << precision) as u64)
        } else {
            Err(DecodeError::MalformedInput {
                offset: 0,
                kind: MalformedKind::ContainerCodestreamMismatch,
            })
        };
        assert_eq!(palette_modulus(precision), expected);
    }
}

#[test]
fn jp2_palette_mapping_preserves_types_channels_and_direct_components() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let jp2 = jp2_with_palette(&codestream, 256, true);
    let image = decode_jp2(&jp2, &DecodeOptions::default()).unwrap();
    assert_eq!(image.components().len(), 3);
    let palette_unsigned = image.component(0).unwrap();
    assert_eq!(palette_unsigned.info().precision, 8);
    assert!(!palette_unsigned.info().signed);
    assert_eq!(
        palette_unsigned.samples(),
        &TypedSamples::Unsigned(vec![42])
    );
    assert_eq!(
        palette_unsigned.channel_definitions()[0].channel_type(),
        crate::image::ChannelType::Color
    );
    assert_eq!(
        palette_unsigned.channel_definitions()[0].association(),
        crate::image::ChannelAssociation::Color(1)
    );

    let palette_signed = image.component(1).unwrap();
    assert_eq!(palette_signed.info().precision, 5);
    assert!(palette_signed.info().signed);
    assert_eq!(palette_signed.samples(), &TypedSamples::Signed(vec![-3]));
    assert_eq!(
        palette_signed.channel_definitions()[0].channel_type(),
        crate::image::ChannelType::Opacity
    );

    let direct = image.component(2).unwrap();
    assert_eq!(direct.info().precision, 8);
    assert_eq!(direct.samples(), &TypedSamples::Unsigned(vec![128]));
    assert_eq!(
        direct.channel_definitions()[0].channel_type(),
        crate::image::ChannelType::Unspecified
    );
    assert_eq!(
        direct.channel_definitions()[0].association(),
        crate::image::ChannelAssociation::Unassociated
    );
}

#[test]
fn jp2_color_decode_has_explicit_bounded_grayscale_output() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let jp2 = jp2_for_codestream(&codestream, 1, 1);
    let image = decode_jp2_color(&jp2, &DecodeOptions::default()).unwrap();
    assert_eq!(image.width(), 1);
    assert_eq!(image.height(), 1);
    assert_eq!(
        image.color_space(),
        crate::color::ConvertedColorSpace::Grayscale
    );
    assert_eq!(image.precision(), 16);
    assert_eq!(image.channel(0).unwrap().samples(), &[32_896]);
}

#[test]
fn selected_color_decode_resamples_signed_subsampled_component() {
    let mut codestream = prepared_codestream(4, 1, 1, &[0, 0x40], &[0]);
    let siz = codestream
        .windows(2)
        .position(|window| window == 0xff51_u16.to_be_bytes())
        .unwrap();
    codestream[siz + 40] = 0x87;
    codestream[siz + 41] = 2;
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;

    let mut jp2 = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jp2.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&4_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[0x87, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jp2.extend(box32(*b"jp2h", &header));
    jp2.extend(box32(*b"jp2c", &codestream));

    let selection = DecodeSelection::full_image().with_region(crate::ImageRegion::new(1, 0, 3, 1));
    let image = decode_jp2_color_selected(&jp2, &DecodeOptions::default(), &selection).unwrap();
    assert_eq!((image.width(), image.height()), (3, 1));
    assert_eq!(
        image.channel(0).unwrap().samples(),
        &[32_896, 32_896, 32_896]
    );
}

#[test]
fn explicitly_selects_typed_jpx_codestream_decode() {
    let mut first = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = first
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    first[cod + 9] = 0;
    let second = first.clone();
    let jpx = jpx_for_codestreams(&[first, second], 1, 1);
    let options = DecodeOptions::default();
    let image = decode_jpx_codestream(&jpx, 1, &options).unwrap();
    assert_eq!(image.width(), 1);
    assert_eq!(image.height(), 1);
    assert_eq!(
        decode_jpx_codestream_selected(&jpx, 1, &options, &DecodeSelection::full_image(),).unwrap(),
        image
    );
    assert!(matches!(
        decode_jpx_codestream(&jpx, 2, &options),
        Err(DecodeError::CodestreamIndexOutOfRange {
            index: 2,
            codestreams: 2,
        })
    ));
    assert!(matches!(
        decode_jp2(&jpx, &options),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidProfile,
            ..
        })
    ));
    let color = decode_jpx_codestream_color(&jpx, 0, &options).unwrap();
    assert_eq!(
        decode_jpx_codestream_color_selected(&jpx, 0, &options, &DecodeSelection::full_image(),)
            .unwrap(),
        color
    );
    assert_eq!(
        color.color_space(),
        crate::color::ConvertedColorSpace::Grayscale
    );
    assert_eq!(color.channel(0).unwrap().samples(), &[32_896]);
    assert_eq!(
        decode_jpx_codestream_color(&jpx, 1, &options).unwrap(),
        color
    );
    let inspection = crate::inspect_jpx_layers(&jpx, options.limits()).unwrap();
    assert_eq!(inspection.layers().len(), 2);
    assert_eq!(
        crate::render_jpx_layer(&jpx, 1, &options)
            .unwrap()
            .channel(0)
            .unwrap()
            .samples(),
        &[32_896]
    );
    assert_eq!(
        crate::render_jpx_composition(&jpx, &options)
            .unwrap()
            .channel(0)
            .unwrap()
            .samples(),
        &[32_896]
    );
    assert!(matches!(
        crate::render_jpx_frame(&jpx, 0, &options),
        Err(DecodeError::FrameIndexOutOfRange {
            index: 0,
            frames: 0,
        })
    ));
}

#[test]
fn applies_part1_component_transform_per_tile() {
    let component = |component, samples| PreparedTileComponent {
        component,
        x: 0,
        y: 0,
        width: 1,
        height: 1,
        fraction_bits: 0,
        samples: vec![samples],
    };
    let mut reversible = vec![component(0, 10), component(1, 4), component(2, 8)];
    apply_prepared_component_transform(&mut reversible, (true, false)).unwrap();
    assert_eq!(
        reversible
            .iter()
            .map(|value| value.samples[0])
            .collect::<Vec<_>>(),
        [15, 7, 11]
    );

    let mut none = vec![component(0, 1), component(1, 2), component(2, 3)];
    apply_prepared_component_transform(&mut none, (false, false)).unwrap();
    assert_eq!(
        none.iter()
            .map(|value| value.samples[0])
            .collect::<Vec<_>>(),
        [1, 2, 3]
    );
}

#[test]
fn applies_ordered_part2_mct_stages_to_raw_jp2_and_selected_jpx_decode() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let codestream =
        add_second_component_mct_stage(add_single_component_mct(codestream, 2, 3), 3, 5);
    let options = DecodeOptions::default();
    let raw = decode_codestream(&codestream, &options).unwrap();
    assert_eq!(
        raw.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![141])
    );

    let jp2 = jp2_for_codestream(&codestream, 1, 1);
    let boxed = decode_jp2(&jp2, &options).unwrap();
    assert_eq!(
        boxed.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![141])
    );
    let jpx = jpx_for_codestreams(&[codestream.clone(), codestream], 1, 1);
    let selected = decode_jpx_codestream(&jpx, 1, &options).unwrap();
    assert_eq!(
        selected.component(0).unwrap().samples(),
        &TypedSamples::Unsigned(vec![141])
    );
}

#[test]
fn inspects_selects_and_renders_static_jpx_layers() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let jpx = jpx_for_compositing_layers(&[codestream.clone(), codestream], 1, 1, false);
    let inspection = crate::inspect_jpx_layers(&jpx, &ResourceLimits::default()).unwrap();
    assert_eq!(inspection.layers().len(), 2);
    assert_eq!(inspection.layer(1).unwrap().codestream_indices(), &[1]);
    assert_eq!(inspection.layer(1).unwrap().horizontal_offset(), 0);
    assert_eq!(inspection.composition().unwrap().width(), 2);

    let selected = crate::render_jpx_layer(&jpx, 1, &DecodeOptions::default()).unwrap();
    assert_eq!(selected.channel(0).unwrap().samples(), &[32_896]);
    let rendered = crate::render_jpx_composition(&jpx, &DecodeOptions::default()).unwrap();
    assert_eq!(rendered.width(), 2);
    assert_eq!(rendered.height(), 1);
    assert_eq!(rendered.channel(0).unwrap().samples(), &[32_896, 0]);
    assert_eq!(rendered.channel(1).unwrap().samples(), &[u16::MAX, 0]);
    let tight = ResourceLimits::default()
        .with_maximum_decoded_bytes(10)
        .unwrap();
    assert!(matches!(
        crate::render_jpx_composition(&jpx, &DecodeOptions::new(tight)),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            ..
        })
    ));
}

#[test]
fn renders_jpx_animation_instructions_and_exposes_timing() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let jpx = jpx_for_compositing_layers(&[codestream], 1, 1, true);
    let inspection = crate::inspect_jpx_layers(&jpx, &ResourceLimits::default()).unwrap();
    let frames = inspection.composition().unwrap().frames();
    assert_eq!(frames.len(), 1);
    assert_eq!(frames[0].duration_milliseconds(), 100);
    let rendered = crate::render_jpx_frame(&jpx, 0, &DecodeOptions::default()).unwrap();
    assert_eq!(rendered.channel(0).unwrap().samples(), &[32_896]);
}

#[test]
fn jp2_palette_mapping_rejects_index_range_and_output_limit() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    let out_of_range = jp2_with_palette(&codestream, 1, false);
    assert!(matches!(
        decode_jp2(&out_of_range, &DecodeOptions::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ContainerCodestreamMismatch,
            ..
        })
    ));

    let mapped = jp2_with_palette(&codestream, 256, false);
    let limits = ResourceLimits::default()
        .with_maximum_decoded_bytes(16)
        .unwrap();
    assert!(matches!(
        decode_jp2(&mapped, &DecodeOptions::new(limits)),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 16,
            actual: 24,
        })
    ));
}

#[test]
fn actual_nonlinear_regions_derive_last_raw_tile_owner_registered_clipping_and_error_order() {
    use crate::codestream::{ComponentInfo, NonlinearPointTransform, Part2Extensions};
    use crate::image::TypedComponent;

    fn wide_ceil(value: u32, divisor: u8, registration: u16) -> Result<u32, DecodeError> {
        if divisor == 0 {
            return Err(invalid_decode());
        }
        let shifted = (u128::from(value) * 65_536).saturating_sub(u128::from(registration));
        let divisor = u128::from(divisor) * 65_536;
        u32::try_from(shifted.div_ceil(divisor)).map_err(|_| arithmetic_overflow())
    }

    fn reference<'a>(
        layout: &'a CodestreamLayout<'_>,
        image: &TypedImage,
        discard_levels: u8,
    ) -> Result<Vec<NonlinearRegion<'a>>, DecodeError> {
        if discard_levels >= 32 {
            return Err(DecodeError::InvalidSelection {
                reason: SelectionError::ReductionTooLarge,
            });
        }
        let scale = 1_u64 << discard_levels;
        let size = &layout.info.image_size;
        let mut regions = Vec::new();
        for component in 0..size.components {
            let info = size.component(component)?;
            let output = image.component(component)?;
            let x0 = wide_ceil(image.x_origin(), info.x_subsampling, info.x_registration)?;
            let y0 = wide_ceil(image.y_origin(), info.y_subsampling, info.y_registration)?;
            let x1 = u32::try_from(u64::from(x0) + u64::from(output.width()))
                .map_err(|_| arithmetic_overflow())?;
            let y1 = u32::try_from(u64::from(y0) + u64::from(output.height()))
                .map_err(|_| arithmetic_overflow())?;
            for tile in 0..size.tile_count()? {
                let tile = u16::try_from(tile).map_err(|_| arithmetic_overflow())?;
                let owner = layout
                    .tile_parts
                    .iter()
                    .rev()
                    .find(|part| part.tile_index == tile)
                    .map_or(&layout.info.part2_extensions, |part| &part.part2_extensions);
                let selected = owner
                    .nonlinear_transforms()
                    .iter()
                    .enumerate()
                    .filter_map(|(index, transform)| {
                        let priority = if transform.component() == Some(component) {
                            0
                        } else if transform.component().is_none() {
                            1
                        } else {
                            return None;
                        };
                        Some((priority, index, transform))
                    })
                    .min_by_key(|(priority, index, _)| (*priority, *index));
                if let Some((_, _, transform)) = selected {
                    let bounds = size.tile_component_bounds(tile, component)?;
                    let start_x = u64::from(bounds.x0).div_ceil(scale).max(u64::from(x0));
                    let start_y = u64::from(bounds.y0).div_ceil(scale).max(u64::from(y0));
                    let end_x = u64::from(bounds.x1).div_ceil(scale).min(u64::from(x1));
                    let end_y = u64::from(bounds.y1).div_ceil(scale).min(u64::from(y1));
                    if start_x < end_x && start_y < end_y {
                        regions.push(NonlinearRegion {
                            component,
                            x0: (start_x - u64::from(x0)) as u32,
                            y0: (start_y - u64::from(y0)) as u32,
                            x1: (end_x - u64::from(x0)) as u32,
                            y1: (end_y - u64::from(y0)) as u32,
                            transform,
                        });
                    }
                }
            }
        }
        Ok(regions)
    }

    fn observe<'a>(
        regions: Vec<NonlinearRegion<'a>>,
    ) -> Vec<(u16, [u32; 4], &'a NonlinearPointTransform)> {
        regions
            .into_iter()
            .map(|region| {
                (
                    region.component,
                    [region.x0, region.y0, region.x1, region.y1],
                    region.transform,
                )
            })
            .collect()
    }

    let extensions = [
        Part2Extensions::default(),
        Part2Extensions::with_nonlinear_transform_for_test(NonlinearPointTransform::for_test(
            7,
            false,
            0,
            None,
            None,
            vec![],
        )),
        Part2Extensions::with_nonlinear_transform_for_test(NonlinearPointTransform::for_test(
            0,
            true,
            u8::MAX,
            Some(u32::MAX),
            Some(0),
            vec![u32::MAX, 0],
        )),
        Part2Extensions::with_nonlinear_transform_for_test(
            NonlinearPointTransform::gamma_for_test(38, true, [u32::MAX, 17, 0, 3, 1]),
        ),
    ];
    let bytes = two_tile_codestream();
    let mut cases = 0;
    let mut nonempty = 0;
    let mut successes = 0;
    for mode in 0..extensions.len() {
        for variant in 0..10 {
            let mut layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
            layout.info.image_size.components = 2;
            layout.info.image_size.component_info[1] = ComponentInfo {
                precision: 0,
                signed: true,
                x_subsampling: 2,
                y_subsampling: 1,
                x_registration: u16::MAX,
                y_registration: 17,
            };
            layout.info.part2_extensions = extensions[1].clone();
            layout.tile_parts[0].part2_extensions = extensions[mode].clone();
            layout.tile_parts[1].part2_extensions =
                extensions[(mode + 1) % extensions.len()].clone();
            match variant {
                0 => {}
                1 => layout.tile_parts.clear(),
                2 => layout.tile_parts.reverse(),
                3 => {
                    let mut duplicate = layout.tile_parts[0].clone();
                    duplicate.part2_extensions = extensions[(mode + 2) % extensions.len()].clone();
                    layout.tile_parts.push(duplicate);
                }
                4 => {
                    for part in &mut layout.tile_parts {
                        part.tile_index = u16::MAX;
                    }
                }
                5 => layout.info.image_size.tiles_across = 0,
                6 => layout.info.image_size.tile_width = 0,
                7 => layout.info.image_size.component_info[0].x_subsampling = 0,
                8 => layout.info.image_size.component_info[0].y_subsampling = 0,
                _ => layout.info.image_size.components = 0,
            }
            for count in 0..4 {
                for (x, y) in [
                    (0, 0),
                    (1, 0),
                    (2, 0),
                    (3, 0),
                    (6, 0),
                    (u32::MAX, 0),
                    (1, u32::MAX),
                ] {
                    for (width, height) in [(0, 0), (1, 1), (4, 1), (u32::MAX, 1)] {
                        let components = (0..count)
                            .map(|_| {
                                TypedComponent::from_parts(
                                    width,
                                    height,
                                    layout.info.image_size.component_info[0],
                                    TypedSamples::Signed(vec![]),
                                )
                            })
                            .collect();
                        let image = TypedImage::for_test(width, height, x, y, components);
                        for discard_levels in [0, 1, 2, 31, 32, 255] {
                            let actual = collect_nonlinear_regions(&layout, &image, discard_levels)
                                .map(observe);
                            let expected = reference(&layout, &image, discard_levels).map(observe);
                            nonempty +=
                                usize::from(matches!(&actual, Ok(regions) if !regions.is_empty()));
                            successes += usize::from(actual.is_ok());
                            assert_eq!(actual, expected);
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 26_880);
    assert!(successes > 100);
    assert!(nonempty > 100);

    let mut layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
    layout.info.image_size.tiles_across = 65_537;
    layout.info.image_size.tiles_down = 1;
    let image = TypedImage::for_test(
        0,
        0,
        0,
        0,
        vec![TypedComponent::from_parts(
            0,
            0,
            layout.info.image_size.component_info[0],
            TypedSamples::Signed(vec![]),
        )],
    );
    assert!(matches!(
        collect_nonlinear_regions(&layout, &image, 0),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::ArithmeticOverflow,
            ..
        })
    ));
    layout.info.image_size.components = 0;
    assert!(
        collect_nonlinear_regions(&layout, &image, 0)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn actual_typed_output_admission_checks_raw_header_and_every_signed_unsigned_plane() {
    use crate::codestream::ComponentInfo;
    use crate::image::{ChannelAssociation, ChannelDefinition, ChannelType, TypedComponent};

    fn component(width: u32, height: u32, count: usize, signed: bool) -> TypedComponent {
        let mut component = TypedComponent::from_parts(
            width,
            height,
            ComponentInfo {
                precision: 0,
                signed: !signed,
                x_subsampling: 0,
                y_subsampling: u8::MAX,
                x_registration: u16::MAX,
                y_registration: 17,
            },
            if signed {
                TypedSamples::Signed(vec![i64::MIN; count])
            } else {
                TypedSamples::Unsigned(vec![u64::MAX; count])
            },
        );
        component.add_channel_definition(ChannelDefinition::new(
            ChannelType::Opacity,
            ChannelAssociation::Color(u16::MAX),
        ));
        component
    }

    let bytes = two_tile_codestream();
    let mut cases = 0;
    let mut successes = 0;
    for input_bytes in [0, 1, usize::MAX] {
        for parts in 0..=2 {
            let mut layout = parse_layout(&bytes, &ResourceLimits::HARDENED).unwrap();
            assert_eq!(layout.tile_parts.len(), 2);
            layout.tile_parts.truncate(parts);
            for expected in [0, 1, 2, u16::MAX] {
                layout.info.image_size.components = expected;
                for (width, height) in [
                    (0, 0),
                    (0, 3),
                    (2, 0),
                    (1, 1),
                    (7, 11),
                    (u32::MAX, u32::MAX),
                ] {
                    for variant in 0..64 {
                        let components = match variant {
                            0 => Vec::new(),
                            61 => vec![component(2, 3, 6, true), component(2, 3, 5, false)],
                            62 => vec![component(2, 3, 5, false), component(2, 3, 6, true)],
                            63 => vec![component(2, 3, 6, true), component(1, 1, 1, false)],
                            _ => {
                                let index = variant - 1;
                                let (w, h) =
                                    [(0, 0), (0, 3), (2, 0), (1, 1), (2, 3), (u32::MAX, u32::MAX)]
                                        [index / 10];
                                vec![component(
                                    w,
                                    h,
                                    [0, 1, 5, 6, 7][index / 2 % 5],
                                    index % 2 == 0,
                                )]
                            }
                        };
                        let image = TypedImage::for_test(width, height, u32::MAX, 17, components);
                        let valid = input_bytes > 0
                            && parts > 0
                            && expected > 0
                            && usize::from(expected) == image.components().len()
                            && width > 0
                            && height > 0
                            && image.components().iter().all(|output| {
                                let count = match output.samples() {
                                    TypedSamples::Signed(values) => values.len(),
                                    TypedSamples::Unsigned(values) => values.len(),
                                };
                                output.width() > 0
                                    && output.height() > 0
                                    && count as u128
                                        == u128::from(output.width()) * u128::from(output.height())
                            });
                        let expected = if valid {
                            Ok(())
                        } else {
                            Err(DecodeError::MalformedInput {
                                offset: 0,
                                kind: MalformedKind::InvalidCodeBlock,
                            })
                        };
                        assert_eq!(
                            validate_part1_output_shape(input_bytes, &layout, &image),
                            expected
                        );
                        cases += 1;
                        successes += usize::from(valid);
                    }
                }
            }
        }
    }
    assert_eq!(cases, 13_824);
    assert_eq!(successes, 60);
}

#[test]
fn output_shape_contracts_reject_empty_components_and_planes() {
    assert!(crate::refinement::decode_output_shape_valid(
        1, 1, 1, 1, 2, 3
    ));
    for (input, parts, expected, actual, width, height) in [
        (0, 1, 1, 1, 2, 3),
        (1, 0, 1, 1, 2, 3),
        (1, 1, 0, 0, 2, 3),
        (1, 1, 1, 2, 2, 3),
        (1, 1, 1, 1, 0, 3),
        (1, 1, 1, 1, 2, 0),
    ] {
        assert!(!crate::refinement::decode_output_shape_valid(
            input, parts, expected, actual, width, height
        ));
    }
    assert!(crate::refinement::component_output_shape_valid(2, 3, 6));
    assert!(!crate::refinement::component_output_shape_valid(0, 3, 0));
    assert!(!crate::refinement::component_output_shape_valid(2, 0, 0));
    assert!(!crate::refinement::component_output_shape_valid(2, 3, 5));
}

#[test]
fn top_level_raw_and_jp2_decode_packed_packet_headers() {
    for ppm in [true, false] {
        let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0]);
        let cod = codestream
            .windows(2)
            .position(|window| window == 0xff52_u16.to_be_bytes())
            .unwrap();
        codestream[cod + 9] = 0;
        let mut packed = pack_packet_header(codestream, ppm, &[0]);
        if ppm {
            let sot = packed
                .windows(2)
                .position(|window| window == 0xff90_u16.to_be_bytes())
                .unwrap();
            packed.splice(sot..sot, segment(0xff57, &[0, 0, 0, 0, 1, 1]));
        }

        let raw = decode_codestream(&packed, &DecodeOptions::default()).unwrap();
        assert_eq!(
            raw.component(0).unwrap().samples(),
            &crate::image::TypedSamples::Unsigned(vec![128])
        );
        let jp2 = jp2_for_codestream(&packed, 1, 1);
        assert_eq!(decode_jp2(&jp2, &DecodeOptions::default()).unwrap(), raw);
    }
}

#[test]
fn top_level_apis_decode_poc_with_plm_plt_and_ppm_ppt() {
    let poc = segment(0xff5f, &[0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 1, 1, 0]);
    for ppm in [true, false] {
        let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x40], &[0, 0]);
        let cod = codestream
            .windows(2)
            .position(|window| window == 0xff52_u16.to_be_bytes())
            .unwrap();
        codestream[cod + 7] = 2;
        codestream[cod + 9] = 0;
        let mut packed = pack_packet_header(codestream, ppm, &[0, 0]);
        let sot = packed
            .windows(2)
            .position(|window| window == 0xff90_u16.to_be_bytes())
            .unwrap();
        packed.splice(sot..sot, poc.clone());
        if ppm {
            let sot = packed
                .windows(2)
                .position(|window| window == 0xff90_u16.to_be_bytes())
                .unwrap();
            packed.splice(sot..sot, segment(0xff57, &[0, 0, 0, 0, 2, 1, 1]));
        } else {
            let sod = packed
                .windows(2)
                .position(|window| window == 0xff93_u16.to_be_bytes())
                .unwrap();
            packed.splice(sod..sod, segment(0xff58, &[0, 1, 1]));
            let sot = packed
                .windows(2)
                .position(|window| window == 0xff90_u16.to_be_bytes())
                .unwrap();
            let eoc = packed.len() - 2;
            let tile_length = u32::try_from(eoc - sot).unwrap();
            packed[sot + 6..sot + 10].copy_from_slice(&tile_length.to_be_bytes());
        }
        let raw = decode_codestream(&packed, &DecodeOptions::default()).unwrap();
        assert_eq!(
            raw.component(0).unwrap().samples(),
            &crate::image::TypedSamples::Unsigned(vec![128])
        );
        let jp2 = jp2_for_codestream(&packed, 1, 1);
        assert_eq!(decode_jp2(&jp2, &DecodeOptions::default()).unwrap(), raw);
    }
}

#[test]
fn sarah_dev_709cd8127b_optional_sop_keeps_raw_selected_and_packed_outputs() {
    let options = DecodeOptions::default();
    let selection = DecodeSelection::full_image();
    let mut cases = 0;
    for flags in [0_u8, 2, 4, 6] {
        for marked in [false, true] {
            if marked && flags & 2 == 0 {
                continue;
            }
            for first in [0_u8, 0x80] {
                let mut header = vec![first];
                if flags & 4 != 0 {
                    header.extend_from_slice(&[0xff, 0x92]);
                }
                for packed in [None, Some(false), Some(true)] {
                    let mut packet = Vec::new();
                    if packed.is_some() {
                        packet.extend_from_slice(&header);
                    }
                    if marked {
                        packet.extend_from_slice(&[0xff, 0x91, 0, 4, 0, 0]);
                    }
                    if packed.is_none() {
                        packet.extend_from_slice(&header);
                    }
                    let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], &packet);
                    let cod = bytes
                        .windows(2)
                        .position(|pair| pair == [0xff, 0x52])
                        .unwrap();
                    bytes[cod + 4] = flags;
                    bytes[cod + 9] = 0;
                    let bytes = match packed {
                        None => bytes,
                        Some(ppm) => pack_packet_header(bytes, ppm, &header),
                    };
                    let snapshot = bytes.clone();
                    let jp2 = jp2_for_codestream(&bytes, 1, 1);
                    let jpx = jpx_for_codestreams(std::slice::from_ref(&bytes), 1, 1);
                    for result in [
                        decode_codestream(&bytes, &options),
                        decode_codestream_selected(&bytes, &options, &selection),
                        decode_jp2(&jp2, &options),
                        decode_jp2_selected(&jp2, &options, &selection),
                        decode_jpx_codestream(&jpx, 0, &options),
                        decode_jpx_codestream_selected(&jpx, 0, &options, &selection),
                    ] {
                        let image = result.unwrap_or_else(|error| {
                            panic!("flags={flags} marked={marked} packed={packed:?} first={first}: {error:?}")
                        });
                        assert_eq!((image.width(), image.height()), (1, 1));
                        assert_eq!(
                            image.component(0).unwrap().samples(),
                            &TypedSamples::Unsigned(vec![128]),
                        );
                        cases += 1;
                    }
                    assert_eq!(bytes, snapshot);
                }
            }
        }
    }
    assert_eq!(cases, 216);
}

#[test]
fn packed_headers_honor_plt_sop_and_eph() {
    let mut codestream = prepared_codestream(
        1,
        1,
        1,
        &[0, 0x40],
        &[0, 0xff, 0x92, 0xff, 0x91, 0, 4, 0, 0],
    );
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 4] = 0x06;
    codestream[cod + 9] = 0;
    let mut packed = pack_packet_header(codestream, false, &[0, 0xff, 0x92]);
    let sod = packed
        .windows(2)
        .position(|window| window == 0xff93_u16.to_be_bytes())
        .unwrap();
    packed.splice(sod..sod, segment(0xff58, &[0, 9]));
    let sot = packed
        .windows(2)
        .position(|window| window == 0xff90_u16.to_be_bytes())
        .unwrap();
    let eoc = packed.len() - 2;
    let tile_length = u32::try_from(eoc - sot).unwrap();
    packed[sot + 6..sot + 10].copy_from_slice(&tile_length.to_be_bytes());
    decode_codestream(&packed, &DecodeOptions::default()).unwrap();

    let sequence = packed
        .windows(2)
        .position(|window| window == 0xff91_u16.to_be_bytes())
        .unwrap();
    packed[sequence + 5] = 1;
    assert!(matches!(
        decode_codestream(&packed, &DecodeOptions::default()),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketHeader,
            ..
        })
    ));
}

#[test]
fn decodes_single_sample_with_empty_detail_resolution_packet() {
    let mut bytes = prepared_codestream(
        1,
        1,
        1,
        &[0x20, 0x48, 0x48, 0x48, 0x48],
        &[0xc0, 0x24, 0x01, 0x07, 0x74, 0x00, 0x00],
    );
    bytes[6..8].copy_from_slice(&0x4000_u16.to_be_bytes());
    let cod = bytes
        .windows(2)
        .position(|marker| marker == [0xff, 0x52])
        .unwrap();
    bytes[cod + 9] = 1;
    bytes[cod + 12] = 0x40;
    bytes.splice(cod..cod, segment(0xff50, &[0, 2, 0, 0, 0, 1]));
    let image = decode_codestream(&bytes, &DecodeOptions::default()).unwrap();
    assert_eq!(
        image.components()[0].samples(),
        &TypedSamples::Unsigned(vec![0])
    );

    let empty_packet = bytes.len() - 3;
    bytes[empty_packet] = 0x80;
    let present = decode_codestream(&bytes, &DecodeOptions::default()).unwrap();
    assert_eq!(
        present.components()[0].samples(),
        image.components()[0].samples()
    );
}

#[test]
fn decodes_nonzero_samples_with_leading_zero_bitplanes() {
    // Packet bytes independently encoded from constant 8-bit PGM samples by OpenJPEG 2.4.
    for (value, packet) in [
        (1, &[0xcf, 0xb4, 0x04, 0x09][..]),
        (129, &[0xc0, 0x21, 0x03][..]),
        (200, &[0xcf, 0xb4, 0x08, 0x04, 0x4f][..]),
    ] {
        let mut bytes = prepared_codestream(1, 1, 1, &[0x40, 0x40], packet);
        let cod = bytes
            .windows(2)
            .position(|marker| marker == [0xff, 0x52])
            .unwrap();
        bytes[cod + 9] = 0;
        let image = decode_codestream(&bytes, &DecodeOptions::default()).unwrap();
        assert_eq!(
            image.components()[0].samples(),
            &TypedSamples::Unsigned(vec![value]),
            "sample {value}"
        );
    }
}

#[test]
fn decodes_packet_body_through_inverse_quantization() {
    let limits = ResourceLimits::default();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState::new();
    let mut reader = PacketBitReader::new(&[0xca], &limits).unwrap();
    let contribution = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: Tier1CodingStyle::default(),
        },
        &mut reader,
    )
    .unwrap()
    .unwrap();
    let body = [0; 5];
    let layers = [CodeBlockLayer {
        contribution: &contribution,
        body: &body,
    }];
    let request = CodeBlockDecodeRequest {
        width: 1,
        height: 1,
        significant_bitplanes: 1,
        orientation: SubbandOrientation::Ll,
        style: Tier1CodingStyle::default(),
        layers: &layers,
        quantization_step: QuantizationStep {
            exponent: 0,
            mantissa: 0,
        },
        dynamic_range: 8,
        reversible: true,
        roi_shift: 0,
    };
    let block = decode_code_block(request, &limits).unwrap();
    assert_eq!(block.width(), 1);
    assert_eq!(block.height(), 1);
    assert_eq!(block.samples().len(), 1);

    let subband = decode_subband(
        1,
        1,
        &[PlacedCodeBlock {
            x: 0,
            y: 0,
            request,
        }],
        &limits,
    )
    .unwrap();
    assert_eq!(subband.samples().len(), 1);
}

#[test]
fn decodes_cleanup_only_ht_packet_body_through_inverse_quantization() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState::new();
    let mut reader = PacketBitReader::new(&[0xc8], &limits).unwrap();
    let contribution = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 1,
            tier1_style: style,
        },
        &mut reader,
    )
    .unwrap()
    .unwrap();
    assert_eq!(contribution.new_passes, 1);
    assert_eq!(contribution.data_length, 4);
    let body = [0xfe, 0x00, 0x63, 0x00];
    let layers = [CodeBlockLayer {
        contribution: &contribution,
        body: &body,
    }];
    let block = decode_code_block(
        CodeBlockDecodeRequest {
            width: 1,
            height: 1,
            significant_bitplanes: 1,
            orientation: SubbandOrientation::Ll,
            style,
            layers: &layers,
            quantization_step: QuantizationStep {
                exponent: 0,
                mantissa: 0,
            },
            dynamic_range: 8,
            reversible: true,
            roi_shift: 0,
        },
        &limits,
    )
    .unwrap();
    assert_eq!(block.samples(), &[1]);
}

#[test]
fn decodes_ht_refinement_packet_body_through_inverse_quantization() {
    let limits = ResourceLimits::default();
    let style = Tier1CodingStyle::from_code_block_style(0x40).unwrap();
    let mut inclusion = TagTree::new(1, 1, &limits).unwrap();
    let mut zero_bitplanes = TagTree::new(1, 1, &limits).unwrap();
    let mut state = CodeBlockPacketState::new();
    let mut reader = PacketBitReader::new(&[0xe3, 0x00], &limits).unwrap();
    let contribution = decode_code_block_contribution(
        &mut state,
        &mut inclusion,
        &mut zero_bitplanes,
        CodeBlockPacketContext {
            leaf_x: 0,
            leaf_y: 0,
            layer: 0,
            maximum_zero_bitplanes: 2,
            tier1_style: style,
        },
        &mut reader,
    )
    .unwrap()
    .unwrap();
    assert_eq!(contribution.new_passes, 2);
    assert_eq!(contribution.segment_count(), 2);
    assert_eq!(contribution.data_length, 3);
    let body = [0x00, 0x63, 0x00];
    let layers = [CodeBlockLayer {
        contribution: &contribution,
        body: &body,
    }];
    let block = decode_code_block(
        CodeBlockDecodeRequest {
            width: 1,
            height: 1,
            significant_bitplanes: 2,
            orientation: SubbandOrientation::Ll,
            style,
            layers: &layers,
            quantization_step: QuantizationStep {
                exponent: 0,
                mantissa: 0,
            },
            dynamic_range: 8,
            reversible: true,
            roi_shift: 0,
        },
        &limits,
    )
    .unwrap();
    assert_eq!(block.samples(), &[-3]);
}

#[test]
fn sarah_dev_174ec5fee4_jph_components_do_not_require_specified_colour() {
    for (coding, packet, expected) in [
        (&[0, 0x10][..], &[0xe4, 0xfe, 0x00, 0x63, 0x00][..], 129),
        (&[0, 0x18][..], &[0xf1, 0x80, 0x00, 0x63, 0x00][..], 125),
    ] {
        let mut codestream = prepared_codestream(1, 1, 1, coding, packet);
        let siz = codestream
            .windows(2)
            .position(|bytes| bytes == [0xff, 0x51])
            .unwrap();
        codestream[siz + 4..siz + 6].copy_from_slice(&0x4000_u16.to_be_bytes());
        let cod = codestream
            .windows(2)
            .position(|bytes| bytes == [0xff, 0x52])
            .unwrap();
        codestream.splice(cod..cod, segment(0xff50, &[0, 2, 0, 0, 0, 8]));
        let cod = codestream
            .windows(2)
            .position(|bytes| bytes == [0xff, 0x52])
            .unwrap();
        codestream[cod + 9] = 0;
        codestream[cod + 12] = 0x40;
        let mut ihdr = Vec::new();
        ihdr.extend_from_slice(&1_u32.to_be_bytes());
        ihdr.extend_from_slice(&1_u32.to_be_bytes());
        ihdr.extend_from_slice(&1_u16.to_be_bytes());
        ihdr.extend_from_slice(&[7, 7, 1, 0]);
        let unspecified_header = box32(*b"ihdr", &ihdr);
        let mut specified_header = unspecified_header.clone();
        specified_header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
        let wrap = |header: &[u8]| {
            let mut file = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
            file.extend(box32(*b"ftyp", b"jph \0\0\0\0jph "));
            file.extend(box32(*b"jp2h", header));
            file.extend(box32(*b"jp2c", &codestream));
            file
        };
        let options = DecodeOptions::default();
        let specified = wrap(&specified_header);
        let control = decode_jph(&specified, &options).unwrap();
        assert_eq!(
            control.component(0).unwrap().samples(),
            &crate::image::TypedSamples::Unsigned(vec![expected])
        );
        let unspecified = wrap(&unspecified_header);
        let inspected = crate::jp2::inspect_jph(&unspecified, options.limits()).unwrap();
        let header = inspected.file().header();
        assert_eq!(header.color.method(), crate::jp2::ColorMethod::Unspecified);
        assert_eq!(header.color.icc_profile(), None);
        assert_eq!(
            (header.color.precedence, header.color.approximation),
            (0, 0)
        );
        assert_eq!(header.nested_box_count, 1);
        let actual = decode_jph(&unspecified, &options).unwrap();
        assert_eq!(actual, control);
        assert_eq!(
            super::decode_jph_color(&unspecified, &options),
            Err(DecodeError::UnsupportedColorConversion {
                reason: crate::UnsupportedColorConversion::UnspecifiedColorSpace,
            })
        );
        for selection in [DecodeSelection::full_image(), DecodeSelection::tile(0)] {
            assert_eq!(
                super::decode_jph_selected(&unspecified, &options, &selection).unwrap(),
                control
            );
            assert_eq!(
                super::decode_jph_color_selected(&unspecified, &options, &selection),
                Err(DecodeError::UnsupportedColorConversion {
                    reason: crate::UnsupportedColorConversion::UnspecifiedColorSpace,
                })
            );
        }
    }
}

#[test]
fn top_level_jph_decodes_cleanup_only_ht_coefficients() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x10], &[0xe4, 0xfe, 0x00, 0x63, 0x00]);
    let siz = codestream
        .windows(2)
        .position(|window| window == 0xff51_u16.to_be_bytes())
        .unwrap();
    codestream[siz + 4..siz + 6].copy_from_slice(&0x4000_u16.to_be_bytes());
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream.splice(cod..cod, segment(0xff50, &[0, 2, 0, 0, 0, 8]));
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    codestream[cod + 12] = 0x40;

    let mut jph = jp2_for_codestream(&codestream, 1, 1);
    jph[20..24].copy_from_slice(b"jph ");
    jph[28..32].copy_from_slice(b"jph ");
    let image = decode_jph(&jph, &DecodeOptions::default()).unwrap();
    assert_eq!(
        image.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![129])
    );
}

#[test]
fn top_level_raw_and_jph_decode_ht_refinement() {
    let mut codestream = prepared_codestream(1, 1, 1, &[0, 0x18], &[0xf1, 0x80, 0x00, 0x63, 0x00]);
    let siz = codestream
        .windows(2)
        .position(|window| window == 0xff51_u16.to_be_bytes())
        .unwrap();
    codestream[siz + 4..siz + 6].copy_from_slice(&0x4000_u16.to_be_bytes());
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream.splice(cod..cod, segment(0xff50, &[0, 2, 0, 0, 0, 8]));
    let cod = codestream
        .windows(2)
        .position(|window| window == 0xff52_u16.to_be_bytes())
        .unwrap();
    codestream[cod + 9] = 0;
    codestream[cod + 12] = 0x40;

    let raw = decode_codestream(&codestream, &DecodeOptions::default()).unwrap();
    let mut jph = jp2_for_codestream(&codestream, 1, 1);
    jph[20..24].copy_from_slice(b"jph ");
    jph[28..32].copy_from_slice(b"jph ");
    let wrapped = decode_jph(&jph, &DecodeOptions::default()).unwrap();
    assert_eq!(wrapped, raw);
    assert_eq!(
        wrapped.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![125])
    );
}

#[test]
fn derives_multiresolution_subbands_and_expounded_steps() {
    let limits = ResourceLimits::default();
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let bytes = prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]);
    let layout = parse_layout(&bytes, &limits).unwrap();
    let subbands = derive_component_subbands(
        &layout.info.image_size,
        layout.info.coding_style,
        &layout.info.quantization,
        0,
    )
    .unwrap();
    assert_eq!(subbands.len(), 7);
    assert_eq!(
        subbands
            .iter()
            .map(|band| (band.orientation, band.width, band.height))
            .collect::<Vec<_>>(),
        vec![
            (SubbandOrientation::Ll, 2, 1),
            (SubbandOrientation::Hl, 1, 1),
            (SubbandOrientation::Lh, 2, 1),
            (SubbandOrientation::Hh, 1, 1),
            (SubbandOrientation::Hl, 2, 2),
            (SubbandOrientation::Lh, 3, 1),
            (SubbandOrientation::Hh, 2, 1),
        ]
    );
    assert_eq!(subbands[0].quantization_index, 0);
    assert_eq!(subbands[6].quantization_index, 6);
    assert_eq!(subbands[6].quantization_step.exponent, 10);
}

#[test]
fn derives_scalar_quantization_steps_by_resolution() {
    let limits = ResourceLimits::default();
    let encoded = (10_u16 << 11) | 5;
    let mut qcd = vec![0x41];
    qcd.extend_from_slice(&encoded.to_be_bytes());
    let bytes = prepared_codestream(5, 3, 0, &qcd, &[0, 0, 0]);
    let layout = parse_layout(&bytes, &limits).unwrap();
    let (index, step) =
        quantization_step_for_subband(&layout.info.quantization, 2, SubbandOrientation::Hh)
            .unwrap();
    assert_eq!(index, 6);
    assert_eq!(step.exponent, 9);
    assert_eq!(step.mantissa, 5);
}

#[test]
fn progression_plan_routes_all_subbands_and_prepares_image() {
    let limits = ResourceLimits::default();
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let bytes = prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]);
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(
        layout.info.coding_style.progression_order,
        ProgressionOrder::Lrcp
    );
    let mut plan = plan_progression_tile(
        &layout.info.image_size,
        layout.info.coding_style,
        &layout.info.quantization,
        &limits,
    )
    .unwrap();
    assert_eq!(plan.components()[0].subbands().len(), 7);
    assert_eq!(plan.components()[0].placements().len(), 7);
    assert_eq!(plan.precincts().len(), 3);
    assert_eq!(plan.precincts()[0].subband_count(), 1);
    assert_eq!(plan.precincts()[1].subband_count(), 3);
    let (grid, precincts) = plan.packet_execution();
    let decoded =
        decode_progression_tile_packets(&layout.tile_parts, grid, precincts, &limits).unwrap();
    assert_eq!(decoded.packets, 3);
    assert_eq!(decoded.present_packets, 0);
    let image = decode_progression_prepared_image(&layout.info.image_size, &plan, &limits).unwrap();
    assert_eq!(image.width(), 5);
    assert_eq!(image.height(), 3);
    assert_eq!(image.component(0).unwrap().samples(), &[0; 15]);
}

#[test]
fn progression_uses_plt_boundaries_to_slice_retained_packets() {
    let limits = ResourceLimits::default();
    let qcd = [0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50];
    let bytes = add_plt(prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]), &[1, 1, 1]);
    let layout = parse_layout(&bytes, &limits).unwrap();
    assert_eq!(layout.tile_parts[0].packet_lengths.packet_count(), 3);
    let mut plan = plan_progression_tile(
        &layout.info.image_size,
        layout.info.coding_style,
        &layout.info.quantization,
        &limits,
    )
    .unwrap();
    let (grid, precincts) = plan.packet_execution();
    let decoded =
        decode_progression_tile_packets(&layout.tile_parts, grid, precincts, &limits).unwrap();
    assert_eq!(decoded.packets, 3);
    assert_eq!(decoded.payload_bytes, 3);

    let invalid_bytes = add_plt(prepared_codestream(5, 3, 1, &qcd, &[0, 0, 0]), &[2, 1]);
    let invalid_layout = parse_layout(&invalid_bytes, &limits).unwrap();
    let mut invalid_plan = plan_progression_tile(
        &invalid_layout.info.image_size,
        invalid_layout.info.coding_style,
        &invalid_layout.info.quantization,
        &limits,
    )
    .unwrap();
    let (grid, precincts) = invalid_plan.packet_execution();
    assert!(matches!(
        decode_progression_tile_packets(&invalid_layout.tile_parts, grid, precincts, &limits,),
        Err(DecodeError::MalformedInput {
            kind: MalformedKind::InvalidPacketLength,
            ..
        })
    ));
}

#[test]
fn progression_plan_uses_clipped_multi_tile_bounds() {
    let limits = ResourceLimits::default();
    let bytes = two_tile_codestream();
    let layout = parse_layout(&bytes, &limits).unwrap();
    let left = plan_progression_tile_at(
        &layout.info.image_size,
        0,
        layout.info.coding_style,
        &layout.info.quantization,
        &limits,
    )
    .unwrap();
    let right = plan_progression_tile_at(
        &layout.info.image_size,
        1,
        layout.info.coding_style,
        &layout.info.quantization,
        &limits,
    )
    .unwrap();
    assert_eq!((left.components()[0].x, left.components()[0].width), (0, 2));
    assert_eq!(
        (right.components()[0].x, right.components()[0].width),
        (2, 3)
    );
}

#[test]
fn top_level_decode_assembles_clipped_tiles_and_typed_samples() {
    let image = decode_codestream(&two_tile_codestream(), &DecodeOptions::default()).unwrap();
    assert_eq!((image.width(), image.height()), (5, 1));
    let component = image.component(0).unwrap();
    assert_eq!((component.width(), component.height()), (5, 1));
    assert_eq!(
        component.info(),
        crate::codestream::ComponentInfo {
            precision: 8,
            signed: false,
            x_subsampling: 1,
            y_subsampling: 1,
            x_registration: 0,
            y_registration: 0,
        }
    );
    assert_eq!(
        component.samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 5])
    );
}

#[test]
fn top_level_jp2_decode_returns_typed_image() {
    let codestream = two_tile_codestream();
    let mut bytes = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    bytes.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&1_u32.to_be_bytes());
    image_header.extend_from_slice(&5_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    bytes.extend(box32(*b"jp2h", &header));
    bytes.extend(box32(*b"jp2c", &codestream));
    let image = decode_jp2(&bytes, &DecodeOptions::default()).unwrap();
    assert_eq!((image.width(), image.height()), (5, 1));
    assert_eq!(
        image.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 5])
    );
    let selected =
        decode_jp2_selected(&bytes, &DecodeOptions::default(), &DecodeSelection::tile(1)).unwrap();
    assert_eq!((selected.width(), selected.height()), (3, 1));
    assert_eq!(
        selected.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 3])
    );
}

#[test]
fn complete_native_selection_and_color_context_match_independent_spatial_reference() {
    fn malformed(kind: MalformedKind) -> DecodeError {
        DecodeError::MalformedInput { offset: 0, kind }
    }
    fn selection_error(reason: SelectionError) -> DecodeError {
        DecodeError::InvalidSelection { reason }
    }
    fn bounded(value: u128) -> Result<u32, DecodeError> {
        if value > u128::from(u32::MAX) {
            Err(malformed(MalformedKind::ArithmeticOverflow))
        } else {
            Ok(value as u32)
        }
    }
    fn tile(size: &ImageSize, index: u16) -> Result<[u32; 4], DecodeError> {
        if size.tiles_across == 0
            || u64::from(index) >= u64::from(size.tiles_across) * u64::from(size.tiles_down)
        {
            return Err(malformed(MalformedKind::InvalidImageGeometry));
        }
        let col = u32::from(index) % size.tiles_across;
        let row = u32::from(index) / size.tiles_across;
        let nx = bounded(u128::from(col) * u128::from(size.tile_width))?;
        let nx = bounded(u128::from(nx) + u128::from(size.tile_x_origin))?;
        let ny = bounded(u128::from(row) * u128::from(size.tile_height))?;
        let ny = bounded(u128::from(ny) + u128::from(size.tile_y_origin))?;
        let ix = bounded(u128::from(size.x_origin) + u128::from(size.width))?;
        let iy = bounded(u128::from(size.y_origin) + u128::from(size.height))?;
        let ex = bounded(u128::from(nx) + u128::from(size.tile_width))?;
        let ey = bounded(u128::from(ny) + u128::from(size.tile_height))?;
        let bounds = [
            nx.max(size.x_origin),
            ny.max(size.y_origin),
            ex.min(ix),
            ey.min(iy),
        ];
        if bounds[0] >= bounds[2] || bounds[1] >= bounds[3] {
            Err(malformed(MalformedKind::InvalidImageGeometry))
        } else {
            Ok(bounds)
        }
    }
    fn validate(
        size: &ImageSize,
        request: &DecodeSelection,
    ) -> Result<(Vec<u16>, [u32; 4]), DecodeError> {
        let ix = bounded(u128::from(size.x_origin) + u128::from(size.width))?;
        let iy = bounded(u128::from(size.y_origin) + u128::from(size.height))?;
        let count = u64::from(size.tiles_across) * u64::from(size.tiles_down);
        if size.tiles_across == 0 || count > 65_536 {
            return Err(malformed(MalformedKind::InvalidImageGeometry));
        }
        let explicit = match request.tile_selection() {
            TileSelection::All => vec![],
            TileSelection::Index(index) => vec![*index],
            TileSelection::Set(indices) => {
                if indices.is_empty() {
                    return Err(selection_error(SelectionError::EmptyTileSet));
                }
                indices.clone()
            }
        };
        let mut seen = std::collections::BTreeSet::new();
        for index in &explicit {
            if u64::from(*index) >= count {
                return Err(selection_error(SelectionError::TileOutOfRange));
            }
            if !seen.insert(*index) {
                return Err(selection_error(SelectionError::DuplicateTile));
            }
        }
        if explicit.len() > 1 {
            let rows = explicit
                .iter()
                .map(|value| u32::from(*value) / size.tiles_across)
                .collect::<Vec<_>>();
            let columns = explicit
                .iter()
                .map(|value| u32::from(*value) % size.tiles_across)
                .collect::<Vec<_>>();
            let (r0, r1) = (*rows.iter().min().unwrap(), *rows.iter().max().unwrap());
            let (c0, c1) = (
                *columns.iter().min().unwrap(),
                *columns.iter().max().unwrap(),
            );
            let area = u64::from(r1 - r0 + 1) * u64::from(c1 - c0 + 1);
            if area > u64::from(u32::MAX) || area as usize != explicit.len() {
                return Err(selection_error(SelectionError::NonRectangularTileSet));
            }
            for row in r0..=r1 {
                for col in c0..=c1 {
                    let offset = bounded(u128::from(row) * u128::from(size.tiles_across))?;
                    let index = bounded(u128::from(offset) + u128::from(col))?;
                    if index > u32::from(u16::MAX) {
                        return Err(malformed(MalformedKind::ArithmeticOverflow));
                    }
                    if !seen.contains(&(index as u16)) {
                        return Err(selection_error(SelectionError::NonRectangularTileSet));
                    }
                }
            }
        }
        let region = if let Some(region) = request.region() {
            if region.width == 0 || region.height == 0 {
                return Err(selection_error(SelectionError::EmptyRegion));
            }
            let x1 = u64::from(region.x) + u64::from(region.width);
            let y1 = u64::from(region.y) + u64::from(region.height);
            if x1 > u64::from(u32::MAX)
                || y1 > u64::from(u32::MAX)
                || region.x < size.x_origin
                || region.y < size.y_origin
                || x1 > u64::from(ix)
                || y1 > u64::from(iy)
            {
                return Err(selection_error(SelectionError::RegionOutOfBounds));
            }
            [region.x, region.y, x1 as u32, y1 as u32]
        } else if explicit.is_empty() {
            [size.x_origin, size.y_origin, ix, iy]
        } else {
            let mut region = [ix, iy, size.x_origin, size.y_origin];
            for index in &explicit {
                let bounds = tile(size, *index)?;
                region[0] = region[0].min(bounds[0]);
                region[1] = region[1].min(bounds[1]);
                region[2] = region[2].max(bounds[2]);
                region[3] = region[3].max(bounds[3]);
            }
            region
        };
        let mut selected = vec![];
        for index in 0..count {
            let bounds = tile(size, index as u16)?;
            if bounds[0] < region[2]
                && bounds[2] > region[0]
                && bounds[1] < region[3]
                && bounds[3] > region[1]
            {
                if !explicit.is_empty() && !seen.contains(&(index as u16)) {
                    return Err(selection_error(SelectionError::RegionOutsideSelectedTiles));
                }
                selected.push(index as u16);
            }
        }
        if selected.is_empty() {
            return Err(selection_error(SelectionError::RegionOutsideSelectedTiles));
        }
        Ok((selected, region))
    }
    fn color(
        size: &ImageSize,
        request: &DecodeSelection,
    ) -> Result<(crate::ImageRegion, [u32; 4], u8), DecodeError> {
        let (_, region) = validate(size, request)?;
        let discard = request.discard_levels();
        if discard >= 32 {
            return Err(selection_error(SelectionError::ReductionTooLarge));
        }
        let scale = 2_u64.pow(u32::from(discard));
        let target = region.map(|value| u64::from(value).div_ceil(scale) as u32);
        let mut horizontal = 0;
        let mut vertical = 0;
        for index in 0..size.components {
            let info = size
                .component_info
                .get(usize::from(index))
                .ok_or(malformed(MalformedKind::InvalidImageGeometry))?;
            if info.x_subsampling == 0 || info.y_subsampling == 0 {
                return Err(malformed(MalformedKind::InvalidCodeBlock));
            }
            let x = (i128::from(target[0]) * 65_536 - i128::from(info.x_registration)).max(0);
            let y = (i128::from(target[1]) * 65_536 - i128::from(info.y_registration)).max(0);
            if x % (i128::from(info.x_subsampling) * 65_536) != 0 {
                horizontal = horizontal.max(u32::from(info.x_subsampling));
            }
            if y % (i128::from(info.y_subsampling) * 65_536) != 0 {
                vertical = vertical.max(u32::from(info.y_subsampling));
            }
        }
        let hx = (u64::from(horizontal) * scale).min(u64::from(u32::MAX));
        let hy = (u64::from(vertical) * scale).min(u64::from(u32::MAX));
        let x0 = (i128::from(region[0]) - i128::from(hx))
            .max(0)
            .max(i128::from(size.x_origin)) as u32;
        let y0 = (i128::from(region[1]) - i128::from(hy))
            .max(0)
            .max(i128::from(size.y_origin)) as u32;
        if region[2] < x0 || region[3] < y0 {
            return Err(malformed(MalformedKind::ArithmeticOverflow));
        }
        Ok((
            crate::ImageRegion::new(x0, y0, region[2] - x0, region[3] - y0),
            target,
            discard,
        ))
    }
    let tiles = [
        TileSelection::All,
        TileSelection::Index(0),
        TileSelection::Index(8),
        TileSelection::Index(9),
        TileSelection::Set(vec![]),
        TileSelection::Set(vec![0, 0]),
        TileSelection::Set(vec![0, 4]),
        TileSelection::Set(vec![4, 0, 3, 1]),
        TileSelection::Set(vec![0, 1]),
    ];
    let regions = [
        None,
        Some(crate::ImageRegion::new(3, 5, 1, 1)),
        Some(crate::ImageRegion::new(3, 5, 13, 9)),
        Some(crate::ImageRegion::new(3, 5, 10, 8)),
        Some(crate::ImageRegion::new(3, 5, 0, 1)),
        Some(crate::ImageRegion::new(2, 5, 1, 1)),
        Some(crate::ImageRegion::new(15, 5, 2, 1)),
        Some(crate::ImageRegion::new(u32::MAX, 5, 2, 1)),
    ];
    let mut contexts = 0;
    for variant in 0..8 {
        for tile_selection in &tiles {
            for region in regions {
                for discard in [0, 1, 31, 32] {
                    for count in [0, 1, 64, 65] {
                        for sampling in 0..3 {
                            let info = crate::codestream::ComponentInfo {
                                precision: 0,
                                signed: true,
                                x_subsampling: if sampling == 2 { 0 } else { 2 },
                                y_subsampling: 3,
                                x_registration: u16::MAX,
                                y_registration: 1,
                            };
                            let mut size = ImageSize {
                                width: 13,
                                height: 9,
                                x_origin: 3,
                                y_origin: 5,
                                components: count,
                                uniform_bit_depth: None,
                                uniform_signed: None,
                                tile_width: 5,
                                tile_height: 4,
                                tile_x_origin: 3,
                                tile_y_origin: 5,
                                tiles_across: 3,
                                tiles_down: 3,
                                component_info: [info; 64],
                            };
                            match variant {
                                1 => size.width = 0,
                                2 => size.x_origin = u32::MAX,
                                3 => size.tiles_across = 0,
                                4 => {
                                    size.tiles_across = 65_537;
                                    size.tiles_down = 1;
                                }
                                5 => size.tile_width = 0,
                                6 => size.tile_x_origin = u32::MAX,
                                7 => size.tiles_down = 0,
                                _ => {}
                            }
                            if sampling == 1 {
                                size.component_info[0].x_subsampling = 1;
                                size.component_info[0].y_subsampling = 1;
                            }
                            let request = crate::options::selection_from_parts(
                                tile_selection.clone(),
                                region,
                                discard,
                            );
                            let expected = validate(&size, &request);
                            let actual = validate_selection(&size, &request)
                                .map(|value| (value.tiles, value.region));
                            assert_eq!(
                                actual, expected,
                                "variant={variant} tiles={tile_selection:?} region={region:?}"
                            );
                            let expected = color(&size, &request);
                            let actual = color_selection_for_size(&size, &request).map(
                                |(selection, target)| {
                                    assert!(matches!(
                                        selection.tile_selection(),
                                        TileSelection::All
                                    ));
                                    (
                                        selection.region().unwrap(),
                                        target,
                                        selection.discard_levels(),
                                    )
                                },
                            );
                            assert_eq!(
                                actual, expected,
                                "variant={variant} discard={discard} count={count} sampling={sampling}"
                            );
                            contexts += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(contexts, 27_648);
}

#[test]
fn associated_native_output_composes_actual_metadata_color_crop_and_none_bypass() {
    let header = jp2::Jp2Header {
        image: jp2::ImageHeader {
            width: u32::MAX,
            height: 0,
            components: 0,
            bit_depth: jp2::ComponentBitDepth::Variable,
            unknown_color_space: true,
            intellectual_property: false,
        },
        color: jp2::ColorSpecification::enumerated(17),
        nested_box_count: u32::MAX,
        palette_entries: u16::MAX,
        palette_columns: u8::MAX,
        component_mapping_entries: u16::MAX,
        channel_definitions: u16::MAX,
        palette: None,
        component_mappings: vec![],
        channel_definition_records: vec![],
        capture_resolution: None,
        display_resolution: None,
    };
    let info = crate::codestream::ComponentInfo {
        precision: 8,
        signed: false,
        x_subsampling: 1,
        y_subsampling: 1,
        x_registration: 0,
        y_registration: 0,
    };
    let image = || {
        TypedImage::for_test(
            2,
            1,
            7,
            11,
            vec![TypedComponent::from_parts(
                2,
                1,
                info,
                TypedSamples::Unsigned(vec![0, 255]),
            )],
        )
    };
    let limits = ResourceLimits::default();
    let (mapped, selected_header) =
        apply_associated_output(image(), Some(&header), &limits).unwrap();
    assert_eq!(selected_header, Some(&header));
    assert_eq!(
        (
            mapped.width(),
            mapped.height(),
            mapped.x_origin(),
            mapped.y_origin()
        ),
        (2, 1, 7, 11)
    );
    assert_eq!(
        mapped.components()[0].samples(),
        &TypedSamples::Unsigned(vec![0, 255])
    );
    let converted = convert_associated_color(&mapped, selected_header, &limits).unwrap();
    assert_eq!((converted.width(), converted.height()), (2, 1));
    assert_eq!(converted.channels()[0].samples(), &[0, u16::MAX]);
    let cropped =
        convert_associated_selected_color(&mapped, selected_header, [8, 11, 9, 12], &limits)
            .unwrap();
    assert_eq!((cropped.width(), cropped.height()), (1, 1));
    assert_eq!(cropped.channels()[0].samples(), &[u16::MAX]);
    assert_eq!(
        finish_associated_selected_output(image(), Some(&header), [8, 11, 9, 12], &limits),
        Ok(cropped),
    );
    let missing = DecodeError::MalformedInput {
        offset: 0,
        kind: MalformedKind::MissingRequiredStructure,
    };
    assert_eq!(
        convert_associated_color(&mapped, None, &limits),
        Err(missing)
    );
    assert_eq!(
        convert_associated_selected_color(&mapped, None, [u32::MAX; 4], &limits),
        Err(missing)
    );
    assert_eq!(
        finish_associated_selected_output(image(), None, [u32::MAX; 4], &limits),
        Err(missing)
    );
    let malformed = || {
        TypedImage::for_test(
            2,
            1,
            u32::MAX,
            u32::MAX,
            vec![TypedComponent::from_parts(
                3,
                0,
                crate::codestream::ComponentInfo {
                    precision: 0,
                    ..info
                },
                TypedSamples::Signed(vec![i64::MIN]),
            )],
        )
    };
    let (unchanged, selected_header) = apply_associated_output(malformed(), None, &limits).unwrap();
    assert_eq!(unchanged, malformed());
    assert_eq!(selected_header, None);
    assert_eq!(
        apply_associated_output(malformed(), Some(&header), &limits),
        Err(DecodeError::MalformedInput {
            offset: 0,
            kind: MalformedKind::ArithmeticOverflow
        })
    );
    let tiny = limits.with_maximum_decoded_bytes(1).unwrap();
    assert_eq!(
        apply_associated_output(image(), Some(&header), &tiny),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 16
        })
    );
    assert_eq!(
        finish_associated_selected_output(image(), Some(&header), [u32::MAX; 4], &tiny),
        Err(DecodeError::LimitExceeded {
            resource: Resource::DecodedBytes,
            limit: 1,
            actual: 16
        }),
    );
}

#[test]
fn selected_tiles_and_regions_match_full_decode_crops() {
    let codestream = two_tile_codestream();
    let options = DecodeOptions::default();
    let full = decode_codestream(&codestream, &options).unwrap();
    let selected_tile =
        decode_codestream_selected(&codestream, &options, &DecodeSelection::tile(1)).unwrap();
    assert_eq!((selected_tile.width(), selected_tile.height()), (3, 1));
    assert_eq!(
        selected_tile.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 3])
    );
    let region = DecodeSelection::full_image().with_region(crate::ImageRegion::new(2, 0, 3, 1));
    let selected_region = decode_codestream_selected(&codestream, &options, &region).unwrap();
    assert_eq!((selected_region.width(), selected_region.height()), (3, 1));
    let crate::image::TypedSamples::Unsigned(full_samples) = full.component(0).unwrap().samples()
    else {
        panic!("expected unsigned fixture samples");
    };
    assert_eq!(
        selected_region.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(full_samples[1..4].to_vec())
    );
}

#[test]
fn sarah_dev_355fe751f9_reduced_tile_nlt_uses_native_coordinates() {
    fn grid(origin: [u32; 2], sampling: [u8; 2]) -> Vec<u8> {
        let mut siz = 0_u16.to_be_bytes().to_vec();
        for value in [16_u32, 16, origin[0], origin[1], 8, 8, 0, 0] {
            siz.extend_from_slice(&value.to_be_bytes());
        }
        siz.extend_from_slice(&1_u16.to_be_bytes());
        siz.extend_from_slice(&[7, sampling[0], sampling[1]]);
        let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
        bytes.extend(segment(0xff51, &siz));
        bytes.extend(segment(0xff52, &[0, 0, 0, 1, 0, 2, 0, 0, 0, 1]));
        bytes.extend(segment(0xff5c, &[0x40; 8]));
        for (tile, slope) in [1_u8, 2, 4, 8].into_iter().enumerate() {
            let tile_x = u32::try_from(tile % 2).unwrap() * 8;
            let tile_y = u32::try_from(tile / 2).unwrap() * 8;
            let packets = [4_u32, 2, 1]
                .into_iter()
                .filter(|scale| {
                    let dx = u32::from(sampling[0]) * scale;
                    let dy = u32::from(sampling[1]) * scale;
                    tile_x.max(origin[0]).div_ceil(dx) < (tile_x + 8).div_ceil(dx)
                        && tile_y.max(origin[1]).div_ceil(dy) < (tile_y + 8).div_ceil(dy)
                })
                .count();
            let mut nonlinear = vec![255, 255, 7, 1];
            for value in [1_u8, slope, 1, 1, 0] {
                nonlinear.extend_from_slice(&[value, 0, 0]);
            }
            let nonlinear = segment(0xff76, &nonlinear);
            let mut sot = u16::try_from(tile).unwrap().to_be_bytes().to_vec();
            sot.extend_from_slice(
                &u32::try_from(14 + nonlinear.len() + packets)
                    .unwrap()
                    .to_be_bytes(),
            );
            sot.extend_from_slice(&[0, 1]);
            bytes.extend(segment(0xff90, &sot));
            bytes.extend(nonlinear);
            bytes.extend_from_slice(&[255, 147]);
            bytes.extend(std::iter::repeat_n(0, packets));
        }
        bytes.extend_from_slice(&[255, 217]);
        bytes
    }

    let options = DecodeOptions::default();
    let mut cases = 0;
    let mut color_cases = 0;
    for origin in [[0_u32, 0], [1, 1], [3, 1]] {
        for sampling in [[1_u8, 1], [2, 2], [3, 2]] {
            let bytes = grid(origin, sampling);
            let snapshot = bytes.clone();
            let width = 16 - origin[0];
            let height = 16 - origin[1];
            let jp2 = jp2_for_codestream(&bytes, width, height);
            let jpx = jpx_for_codestreams(std::slice::from_ref(&bytes), width, height);
            let maximum_discard = if sampling == [1, 1] { 2 } else { 1 };
            for discard in 0..=maximum_discard {
                let scale = 1_u32 << discard;
                for (selection, bounds) in [
                    (
                        DecodeSelection::full_image(),
                        [origin[0], origin[1], 16, 16],
                    ),
                    (DecodeSelection::tile(3), [8, 8, 16, 16]),
                    (DecodeSelection::tiles(vec![3, 1]), [8, origin[1], 16, 16]),
                    (
                        DecodeSelection::full_image()
                            .with_region(crate::ImageRegion::new(5, 3, 10, 12)),
                        [5, 3, 15, 15],
                    ),
                ] {
                    let selection = selection.with_discard_levels(discard);
                    let before = selection.clone();
                    let [x0, y0, x1, y1] = bounds.map(|value| value.div_ceil(scale));
                    let dx = u32::from(sampling[0]) * scale;
                    let dy = u32::from(sampling[1]) * scale;
                    let cx0 = bounds[0].div_ceil(dx);
                    let cy0 = bounds[1].div_ceil(dy);
                    let cx1 = bounds[2].div_ceil(dx);
                    let cy1 = bounds[3].div_ceil(dy);
                    let mut expected = Vec::new();
                    for y in cy0..cy1 {
                        for x in cx0..cx1 {
                            let tile = (y * dy / 8) * 2 + x * dx / 8;
                            expected.push(128_u64 / [1, 2, 4, 8][tile as usize]);
                        }
                    }
                    for result in [
                        decode_codestream_selected(&bytes, &options, &selection),
                        decode_jp2_selected(&jp2, &options, &selection),
                        decode_jpx_codestream_selected(&jpx, 0, &options, &selection),
                    ] {
                        let image = result.unwrap();
                        assert_eq!(
                            (
                                image.x_origin(),
                                image.y_origin(),
                                image.width(),
                                image.height()
                            ),
                            (x0, y0, x1 - x0, y1 - y0),
                        );
                        let component = image.component(0).unwrap();
                        assert_eq!(
                            (component.width(), component.height()),
                            (cx1 - cx0, cy1 - cy0)
                        );
                        assert_eq!(
                            component.samples(),
                            &TypedSamples::Unsigned(expected.clone()),
                            "origin={origin:?} sampling={sampling:?} discard={discard} bounds={bounds:?}",
                        );
                        assert_eq!(component.info().x_subsampling, sampling[0]);
                        assert_eq!(component.info().y_subsampling, sampling[1]);
                        cases += 1;
                    }
                    if sampling == [1, 1] {
                        let expected_color: Vec<_> = expected
                            .iter()
                            .map(|value| u16::try_from(*value).unwrap() * 257)
                            .collect();
                        for result in [
                            decode_jp2_color_selected(&jp2, &options, &selection),
                            decode_jpx_codestream_color_selected(&jpx, 0, &options, &selection),
                        ] {
                            let image = result.unwrap();
                            assert_eq!((image.width(), image.height()), (x1 - x0, y1 - y0));
                            assert_eq!(image.channel(0).unwrap().samples(), expected_color);
                            color_cases += 1;
                        }
                    }
                    assert_eq!(selection, before);
                }
            }
            assert_eq!(bytes, snapshot);
        }
    }
    assert_eq!(cases, 252);
    assert_eq!(color_cases, 72);
}

#[test]
fn reduced_selection_uses_native_resolution_and_selected_limits() {
    let codestream = prepared_codestream(
        5,
        3,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    let limits = ResourceLimits::default()
        .with_maximum_packets(2)
        .unwrap()
        .with_maximum_decoded_bytes(64)
        .unwrap();
    let options = DecodeOptions::new(limits);
    assert!(matches!(
        decode_codestream(&codestream, &options),
        Err(DecodeError::LimitExceeded {
            resource: Resource::Packets,
            ..
        })
    ));
    let reduced = decode_codestream_selected(
        &codestream,
        &options,
        &DecodeSelection::full_image().with_discard_levels(1),
    )
    .unwrap();
    assert_eq!((reduced.width(), reduced.height()), (3, 2));
    assert_eq!(
        reduced.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 6])
    );
}

#[test]
fn selected_decode_rejects_malformed_selection_deterministically() {
    let codestream = two_tile_codestream();
    let options = DecodeOptions::default();
    let cases = [
        (
            DecodeSelection::tiles(Vec::new()),
            SelectionError::EmptyTileSet,
        ),
        (
            DecodeSelection::tiles(vec![0, 0]),
            SelectionError::DuplicateTile,
        ),
        (DecodeSelection::tile(2), SelectionError::TileOutOfRange),
        (
            DecodeSelection::full_image().with_region(crate::ImageRegion::new(0, 0, 1, 1)),
            SelectionError::RegionOutOfBounds,
        ),
        (
            DecodeSelection::tile(0).with_region(crate::ImageRegion::new(3, 0, 1, 1)),
            SelectionError::RegionOutsideSelectedTiles,
        ),
        (
            DecodeSelection::full_image().with_region(crate::ImageRegion::new(1, 0, 0, 1)),
            SelectionError::EmptyRegion,
        ),
        (
            DecodeSelection::full_image().with_discard_levels(1),
            SelectionError::ReductionTooLarge,
        ),
    ];
    for (selection, reason) in cases {
        assert_eq!(
            decode_codestream_selected(&codestream, &options, &selection),
            Err(DecodeError::InvalidSelection { reason })
        );
    }
}

#[test]
fn top_level_raw_and_jp2_decode_apply_retained_maxshift() {
    let mut codestream = prepared_codestream(
        5,
        3,
        1,
        &[0x40, 0x40, 0x48, 0x48, 0x50, 0x48, 0x48, 0x50],
        &[0, 0, 0],
    );
    let sot = codestream
        .windows(2)
        .position(|bytes| bytes == 0xff90_u16.to_be_bytes())
        .unwrap();
    codestream.splice(sot..sot, segment(0xff5e, &[0, 0, 4]));

    let limits = ResourceLimits::default();
    let layout = parse_layout(&codestream, &limits).unwrap();
    let plan = plan_progression_tile_at_with_roi(
        &layout.info.image_size,
        0,
        layout.info.coding_style,
        &layout.info.quantization,
        &layout.tile_parts[0].roi_shifts,
        &limits,
    )
    .unwrap();
    assert!(
        plan.components()[0]
            .subbands()
            .iter()
            .all(|subband| subband.roi_shift == 4)
    );
    let raw = decode_codestream(&codestream, &DecodeOptions::default()).unwrap();
    assert_eq!(
        raw.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 15])
    );

    let mut jp2 = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jp2.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&3_u32.to_be_bytes());
    image_header.extend_from_slice(&5_u32.to_be_bytes());
    image_header.extend_from_slice(&1_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jp2.extend(box32(*b"jp2h", &header));
    jp2.extend(box32(*b"jp2c", &codestream));
    assert_eq!(decode_jp2(&jp2, &DecodeOptions::default()).unwrap(), raw);
}

#[test]
fn top_level_raw_and_jp2_decode_apply_component_overrides() {
    let codestream = component_override_codestream();
    let limits = ResourceLimits::default();
    let layout = parse_layout(&codestream, &limits).unwrap();
    let mut plan = plan_progression_tile_at_with_component_overrides(
        &layout.info.image_size,
        0,
        layout.info.coding_style,
        &layout.tile_parts[0].component_coding_styles,
        &layout.tile_parts[0].component_quantizations,
        &layout.tile_parts[0].roi_shifts,
        &limits,
    )
    .unwrap();
    assert_eq!(plan.components()[0].subbands().len(), 1);
    assert_eq!(plan.components()[1].subbands().len(), 4);
    assert_eq!(
        plan.components()[0].subbands()[0].quantization_step,
        QuantizationStep {
            exponent: 9,
            mantissa: 5,
        }
    );
    assert_eq!(
        plan.components()[1].subbands()[3]
            .quantization_step
            .exponent,
        10
    );
    assert_eq!(plan.grid().packet_count(), 3);
    let (grid, precincts) = plan.packet_execution();
    decode_progression_tile_packets(&layout.tile_parts, grid, precincts, &limits).unwrap();
    let prepared =
        decode_progression_prepared_image(&layout.info.image_size, &plan, &limits).unwrap();
    assert_eq!(prepared.component(0).unwrap().samples(), &[0; 16]);
    assert_eq!(prepared.component(1).unwrap().samples(), &[0; 16]);

    let raw = decode_codestream(&codestream, &DecodeOptions::default()).unwrap();
    assert_eq!(raw.components().len(), 2);
    assert_eq!(
        raw.component(0).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 16])
    );
    assert_eq!(
        raw.component(1).unwrap().samples(),
        &crate::image::TypedSamples::Unsigned(vec![128; 16])
    );

    let mut jp2 = box32(*b"jP  ", &[0x0d, 0x0a, 0x87, 0x0a]);
    jp2.extend(box32(*b"ftyp", b"jp2 \0\0\0\0jp2 "));
    let mut image_header = Vec::new();
    image_header.extend_from_slice(&4_u32.to_be_bytes());
    image_header.extend_from_slice(&4_u32.to_be_bytes());
    image_header.extend_from_slice(&2_u16.to_be_bytes());
    image_header.extend_from_slice(&[7, 7, 0, 0]);
    let mut header = box32(*b"ihdr", &image_header);
    header.extend(box32(*b"colr", &[1, 0, 0, 0, 0, 0, 17]));
    jp2.extend(box32(*b"jp2h", &header));
    jp2.extend(box32(*b"jp2c", &codestream));
    assert_eq!(decode_jp2(&jp2, &DecodeOptions::default()).unwrap(), raw);
}

fn component_override_codestream() -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&4_u32.to_be_bytes());
    siz.extend_from_slice(&4_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&4_u32.to_be_bytes());
    siz.extend_from_slice(&4_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&2_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1, 7, 1, 1]);
    let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
    bytes.extend(segment(0xff51, &siz));
    bytes.extend(segment(0xff52, &[0, 0, 0, 1, 0, 0, 0, 0, 0, 1]));
    bytes.extend(segment(0xff53, &[1, 0, 1, 0, 0, 0, 1]));
    bytes.extend(segment(0xff5c, &[0x40, 0x40]));
    bytes.extend(segment(0xff5d, &[1, 0x40, 0x40, 0x40, 0x40, 0x40]));
    let tile_start = bytes.len();
    let mut sot = Vec::new();
    sot.extend_from_slice(&0_u16.to_be_bytes());
    sot.extend_from_slice(&0_u32.to_be_bytes());
    sot.extend_from_slice(&[0, 1]);
    bytes.extend(segment(0xff90, &sot));
    let tile_default_step = (9_u16 << 11) | 5;
    let mut tile_qcd = vec![0x41];
    tile_qcd.extend_from_slice(&tile_default_step.to_be_bytes());
    bytes.extend(segment(0xff5c, &tile_qcd));
    bytes.extend(segment(0xff5d, &[1, 0x40, 0x50, 0x50, 0x50, 0x50]));
    bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
    bytes.extend_from_slice(&[0, 0, 0]);
    let length = u32::try_from(bytes.len() - tile_start).unwrap();
    bytes[tile_start + 6..tile_start + 10].copy_from_slice(&length.to_be_bytes());
    bytes.extend_from_slice(&0xffd9_u16.to_be_bytes());
    bytes
}

fn two_tile_codestream() -> Vec<u8> {
    let mut siz = Vec::new();
    siz.extend_from_slice(&0_u16.to_be_bytes());
    siz.extend_from_slice(&6_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&3_u32.to_be_bytes());
    siz.extend_from_slice(&1_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&0_u32.to_be_bytes());
    siz.extend_from_slice(&1_u16.to_be_bytes());
    siz.extend_from_slice(&[7, 1, 1]);
    let mut bytes = 0xff4f_u16.to_be_bytes().to_vec();
    bytes.extend(segment(0xff51, &siz));
    bytes.extend(segment(0xff52, &[0, 0, 0, 1, 0, 0, 0, 0, 0, 1]));
    bytes.extend(segment(0xff5c, &[0x40, 0x40]));
    for tile_index in 0_u16..2 {
        let start = bytes.len();
        let mut sot = Vec::new();
        sot.extend_from_slice(&tile_index.to_be_bytes());
        sot.extend_from_slice(&0_u32.to_be_bytes());
        sot.extend_from_slice(&[0, 1]);
        bytes.extend(segment(0xff90, &sot));
        bytes.extend_from_slice(&0xff93_u16.to_be_bytes());
        bytes.push(0);
        let length = u32::try_from(bytes.len() - start).unwrap();
        bytes[start + 6..start + 10].copy_from_slice(&length.to_be_bytes());
    }
    bytes.extend_from_slice(&0xffd9_u16.to_be_bytes());
    bytes
}

fn box32(box_type: [u8; 4], payload: &[u8]) -> Vec<u8> {
    let mut bytes = u32::try_from(8 + payload.len())
        .unwrap()
        .to_be_bytes()
        .to_vec();
    bytes.extend_from_slice(&box_type);
    bytes.extend_from_slice(payload);
    bytes
}
