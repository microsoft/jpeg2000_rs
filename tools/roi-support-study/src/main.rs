#![forbid(unsafe_code)]

use jpeg2000_decoder::{
    ResourceLimits,
    codestream::{self, WaveletTransform},
    decode::plan_progression_tile_at_with_component_overrides,
    packet::decode_progression_tile_packets,
    tier1::SubbandOrientation,
};
use std::{collections::BTreeSet, env, error::Error, fs, ops::Range};

type Interval = Option<Range<u32>>;

#[derive(Clone, Debug)]
struct Rect {
    x: Range<u32>,
    y: Range<u32>,
}

fn intersection(left: &Range<u32>, right: &Range<u32>) -> Interval {
    let start = left.start.max(right.start);
    let end = left.end.min(right.end);
    (start < end).then_some(start..end)
}

fn union(left: Interval, right: Interval) -> Interval {
    match (left, right) {
        (Some(a), Some(b)) => Some(a.start.min(b.start)..a.end.max(b.end)),
        (a, None) | (None, a) => a,
    }
}

fn clamp_support(start: i64, end: i64, domain: &Range<u32>) -> Interval {
    if start >= end || domain.is_empty() {
        return None;
    }
    let first = start.clamp(i64::from(domain.start), i64::from(domain.end - 1));
    let last = (end - 1).clamp(i64::from(domain.start), i64::from(domain.end - 1));
    Some(
        u32::try_from(first).expect("clamped coordinate")
            ..u32::try_from(last + 1).expect("clamped end"),
    )
}

fn split53(required: &Range<u32>, canvas: &Range<u32>) -> (Interval, Interval) {
    let Some(required) = intersection(required, canvas) else {
        return (None, None);
    };
    let low_domain = canvas.start.div_ceil(2)..canvas.end.div_ceil(2);
    let high_domain = canvas.start / 2..canvas.end / 2;
    let selected_low = intersection(
        &(required.start.div_ceil(2)..required.end.div_ceil(2)),
        &low_domain,
    );
    let selected_high = intersection(&(required.start / 2..required.end / 2), &high_domain);
    let predicted_low = selected_high.as_ref().and_then(|high| {
        clamp_support(i64::from(high.start), i64::from(high.end) + 1, &low_domain)
    });
    let low = union(selected_low, predicted_low);
    let update_high = low
        .as_ref()
        .and_then(|low| clamp_support(i64::from(low.start) - 1, i64::from(low.end), &high_domain));
    (low, union(selected_high, update_high))
}

fn rectangle(x: Interval, y: Interval) -> Option<Rect> {
    Some(Rect { x: x?, y: y? })
}

fn intersects(left: &Rect, right: &Rect) -> bool {
    intersection(&left.x, &right.x).is_some() && intersection(&left.y, &right.y).is_some()
}

fn slot(orientation: SubbandOrientation) -> usize {
    match orientation {
        SubbandOrientation::Ll => 0,
        SubbandOrientation::Hl => 1,
        SubbandOrientation::Lh => 2,
        SubbandOrientation::Hh => 3,
    }
}

fn support53(canvas: Rect, requested: Rect, levels: u8) -> Vec<[Option<Rect>; 4]> {
    let mut masks = vec![[None, None, None, None]; usize::from(levels) + 1];
    let mut canvas = canvas;
    let mut required = Some(requested);
    for level in (1..=usize::from(levels)).rev() {
        let (lx, hx, ly, hy) = match &required {
            Some(area) => {
                let (lx, hx) = split53(&area.x, &canvas.x);
                let (ly, hy) = split53(&area.y, &canvas.y);
                (lx, hx, ly, hy)
            }
            None => (None, None, None, None),
        };
        masks[level][slot(SubbandOrientation::Hl)] = rectangle(hx.clone(), ly.clone());
        masks[level][slot(SubbandOrientation::Lh)] = rectangle(lx.clone(), hy.clone());
        masks[level][slot(SubbandOrientation::Hh)] = rectangle(hx, hy);
        required = rectangle(lx, ly);
        canvas = Rect {
            x: canvas.x.start.div_ceil(2)..canvas.x.end.div_ceil(2),
            y: canvas.y.start.div_ceil(2)..canvas.y.end.div_ceil(2),
        };
    }
    masks[0][0] = required;
    masks
}

#[derive(Clone, Copy, Default)]
struct Counts {
    blocks: u64,
    coefficients: u64,
    bytes: u64,
    passes: u64,
}

impl Counts {
    fn add(
        &mut self,
        width: u16,
        height: u16,
        bytes: u64,
        passes: u32,
    ) -> Result<(), Box<dyn Error>> {
        self.blocks = self.blocks.checked_add(1).ok_or("block count overflow")?;
        self.coefficients = self
            .coefficients
            .checked_add(u64::from(width) * u64::from(height))
            .ok_or("coefficient count overflow")?;
        self.bytes = self.bytes.checked_add(bytes).ok_or("byte count overflow")?;
        self.passes = self
            .passes
            .checked_add(u64::from(passes))
            .ok_or("pass count overflow")?;
        Ok(())
    }
}

fn run() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = env::args().skip(1).collect();
    let [path, window] = args.as_slice() else {
        return Err("usage: roi-support-study INPUT x,y,width,height".into());
    };
    let coordinates = window
        .split(',')
        .map(str::parse)
        .collect::<Result<Vec<u32>, _>>()?;
    let [x, y, width, height] = coordinates.as_slice() else {
        return Err("window must have four coordinates".into());
    };
    if *width == 0 || *height == 0 {
        return Err("window dimensions must be positive".into());
    }
    let requested = Rect {
        x: *x..x.checked_add(*width).ok_or("window x overflow")?,
        y: *y..y.checked_add(*height).ok_or("window y overflow")?,
    };
    let input = fs::read(path)?;
    let limits = ResourceLimits::default();
    let layout = codestream::parse_layout(&input, &limits)?;
    let size = &layout.info.image_size;
    if size.components != 1
        || size.component(0)?.x_subsampling != 1
        || size.component(0)?.y_subsampling != 1
    {
        return Err("this first experiment requires one unit-sampled component".into());
    }
    let image_x1 = size
        .x_origin
        .checked_add(size.width)
        .ok_or("image x extent overflow")?;
    let image_y1 = size
        .y_origin
        .checked_add(size.height)
        .ok_or("image y extent overflow")?;
    if requested.x.start < size.x_origin
        || requested.y.start < size.y_origin
        || requested.x.end > image_x1
        || requested.y.end > image_y1
    {
        return Err("window is outside the image reference grid".into());
    }
    let mut seen = BTreeSet::new();
    let mut selected_tiles = 0_u64;
    let mut all = Counts::default();
    let mut outside = Counts::default();
    let mut index = 0;
    println!(
        "tile,resolution,orientation,blocks,coefficients,bytes,passes,outside_blocks,outside_coefficients,outside_bytes,outside_passes"
    );
    while index < layout.tile_parts.len() {
        let first = &layout.tile_parts[index];
        let tile = first.tile_index;
        if !seen.insert(tile) {
            return Err(
                "diagnostic requires contiguous tile parts; no alternate collector is used".into(),
            );
        }
        let mut end = index + 1;
        while end < layout.tile_parts.len() && layout.tile_parts[end].tile_index == tile {
            end += 1;
        }
        let parts = &layout.tile_parts[index..end];
        index = end;
        let bounds = size.tile_bounds(tile)?;
        let canvas = Rect {
            x: bounds.x0..bounds.x1,
            y: bounds.y0..bounds.y1,
        };
        if !intersects(&canvas, &requested) {
            continue;
        }
        let style = first.component_coding_styles.style(0)?;
        if style.transform != WaveletTransform::Reversible5x3
            || style.decomposition_structure.is_some()
        {
            return Err(
                "this mask experiment only models standard isotropic reversible 5/3".into(),
            );
        }
        selected_tiles += 1;
        let masks = support53(canvas, requested.clone(), style.decomposition_levels);
        let mut plan = plan_progression_tile_at_with_component_overrides(
            size,
            tile,
            first.coding_style,
            &first.component_coding_styles,
            &first.component_quantizations,
            &first.roi_shifts,
            &limits,
        )?;
        let (grid, precincts) = plan.packet_execution();
        decode_progression_tile_packets(parts, grid, precincts, &limits)?;
        for component in plan.components() {
            for (band_index, band) in component.subbands().iter().enumerate() {
                let mask = masks
                    .get(usize::from(band.resolution))
                    .ok_or("subband resolution outside mask")?
                    .get(slot(band.orientation))
                    .ok_or("subband orientation outside mask")?;
                let mut counts = Counts::default();
                let mut skipped = Counts::default();
                for placement in component
                    .placements()
                    .iter()
                    .filter(|p| p.subband_index == band_index)
                {
                    let decoder = plan
                        .precincts()
                        .get(placement.precinct_index)
                        .ok_or("precinct index outside plan")?
                        .decoder(placement.decoder_index)?;
                    let plane = decoder.plane();
                    let bx = band.x0.checked_add(placement.x).ok_or("block x overflow")?;
                    let by = band.y0.checked_add(placement.y).ok_or("block y overflow")?;
                    let block = Rect {
                        x: bx..bx
                            .checked_add(u32::from(plane.width()))
                            .ok_or("block extent overflow")?,
                        y: by..by
                            .checked_add(u32::from(plane.height()))
                            .ok_or("block extent overflow")?,
                    };
                    counts.add(
                        plane.width(),
                        plane.height(),
                        decoder.decoded_bytes(),
                        decoder.next_pass(),
                    )?;
                    all.add(
                        plane.width(),
                        plane.height(),
                        decoder.decoded_bytes(),
                        decoder.next_pass(),
                    )?;
                    if !mask.as_ref().is_some_and(|mask| intersects(&block, mask)) {
                        skipped.add(
                            plane.width(),
                            plane.height(),
                            decoder.decoded_bytes(),
                            decoder.next_pass(),
                        )?;
                        outside.add(
                            plane.width(),
                            plane.height(),
                            decoder.decoded_bytes(),
                            decoder.next_pass(),
                        )?;
                    }
                }
                println!(
                    "{},{},{:?},{},{},{},{},{},{},{},{}",
                    tile,
                    band.resolution,
                    band.orientation,
                    counts.blocks,
                    counts.coefficients,
                    counts.bytes,
                    counts.passes,
                    skipped.blocks,
                    skipped.coefficients,
                    skipped.bytes,
                    skipped.passes
                );
            }
        }
    }
    if selected_tiles == 0 {
        return Err("no selected tile was observed".into());
    }
    eprintln!(
        "diagnostic_only=true tiles_seen={} selected_tiles={} decoded_blocks={} outside_blocks={} decoded_coefficients={} outside_coefficients={} decoded_bytes={} outside_bytes={} decoded_passes={} outside_passes={}",
        seen.len(),
        selected_tiles,
        all.blocks,
        outside.blocks,
        all.coefficients,
        outside.coefficients,
        all.bytes,
        outside.bytes,
        all.passes,
        outside.passes
    );
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ROI support experiment failed: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use jpeg2000_decoder::transform::inverse_5_3;

    #[test]
    fn support_preserves_every_small_interval_including_odd_origins_and_singletons() {
        for origin in 0_u32..4 {
            for length in 1..25 {
                let canvas = origin..origin + length;
                let low_domain = origin.div_ceil(2)..(origin + length).div_ceil(2);
                let high_domain = origin / 2..(origin + length) / 2;
                let low: Vec<i64> = low_domain
                    .clone()
                    .map(|x| (i64::from(x) * 31 + 7) % 101 - 50)
                    .collect();
                let high: Vec<i64> = high_domain
                    .clone()
                    .map(|x| (i64::from(x) * 17 + 3) % 83 - 40)
                    .collect();
                let expected = inverse_5_3(&low, &high, origin % 2 == 0).unwrap();
                for start in canvas.clone() {
                    for end in start + 1..=canvas.end {
                        let (needed_low, needed_high) = split53(&(start..end), &canvas);
                        let masked = |values: &[i64], domain: &Range<u32>, needed: &Interval| {
                            domain
                                .clone()
                                .zip(values)
                                .map(|(x, &value)| {
                                    if needed.as_ref().is_some_and(|r| r.contains(&x)) {
                                        value
                                    } else {
                                        0
                                    }
                                })
                                .collect::<Vec<_>>()
                        };
                        let actual = inverse_5_3(
                            &masked(&low, &low_domain, &needed_low),
                            &masked(&high, &high_domain, &needed_high),
                            origin % 2 == 0,
                        )
                        .unwrap();
                        assert_eq!(
                            actual[(start - origin) as usize..(end - origin) as usize],
                            expected[(start - origin) as usize..(end - origin) as usize]
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn full_window_cannot_discard_any_subband_coefficients() {
        let canvas = Rect { x: 3..66, y: 1..50 };
        let masks = support53(canvas.clone(), canvas, 4);
        assert_eq!(masks[0][0].as_ref().unwrap().x, 1..5);
        for level in masks.iter().skip(1) {
            assert!(level[1..].iter().all(Option::is_some));
        }
    }
}
