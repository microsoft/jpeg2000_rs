use jpeg2000_decoder::{
    COOPERATIVE_DEADLINES_ENABLED, ChannelType, DecodeError, DecodeOptions, DecodeSelection,
    MalformedKind, TypedImage, TypedSamples, codestream, jp2,
};

const PREFIX_PLANES: usize = 4;

#[repr(C)]
pub struct Header {
    x0: u32,
    y0: u32,
    x1: u32,
    y1: u32,
    count: u32,
    color: i32,
    filled: u32,
    prefix: [Plane; PREFIX_PLANES],
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Plane {
    width: u32,
    height: u32,
    precision: u32,
    signed: u32,
    dx: u32,
    dy: u32,
    alpha: u32,
}

unsafe fn input<'a>(data: *const u8, size: usize) -> Option<&'a [u8]> {
    if data.is_null() || size == 0 || size > 16 * 1024 * 1024 {
        return None;
    }
    // The C adapter owns this allocation for the duration of the call.
    Some(unsafe { std::slice::from_raw_parts(data, size) })
}

// The caller must have validated lenient input with the crate's recovery API
// before reopening the JP2 metadata prefix.
fn parse_container<'a>(
    data: &'a [u8],
    limits: &jpeg2000_decoder::ResourceLimits,
    recovered: bool,
) -> Option<jp2::Jp2File<'a>> {
    match jp2::parse(data, limits) {
        Ok(file) => Some(file),
        Err(DecodeError::MalformedInput {
            offset,
            kind: MalformedKind::InvalidBoxLength | MalformedKind::TrailingData,
        }) if recovered => {
            let (prefix, suffix) = data.split_at_checked(usize::try_from(offset).ok()?)?;
            if !prefix.ends_with(&[0xff, 0xd9]) || !matches!(suffix, b"\r" | b"\n" | b"\r\n") {
                return None;
            }
            jp2::parse(prefix, limits).ok()
        }
        Err(_) => None,
    }
}

fn inspect(data: &[u8], boxed: bool, strict: bool) -> Option<(codestream::ImageSize, i32)> {
    let options = DecodeOptions::default();
    let limits = options.limits();
    let recovered = if strict {
        None
    } else {
        Some(jpeg2000_decoder::inspect_pdf_compatible(data, &options).ok()?)
    };
    let (stream, color) = if boxed {
        let file = parse_container(data, limits, recovered.is_some())?;
        if (strict && file.file_type().brand != jp2::BoxType::JP2_BRAND)
            || file.codestream_count() != 1
        {
            return None;
        }
        let color = match file.header.color.method {
            jp2::ColorMethod::Enumerated { color_space: 16 } => 1,
            jp2::ColorMethod::Enumerated { color_space: 17 } => 2,
            jp2::ColorMethod::Enumerated { color_space: 18 } => 3,
            jp2::ColorMethod::Enumerated { color_space: 12 } => 5,
            _ => 0,
        };
        (file.codestream(0).ok()?.data(), color)
    } else {
        if !data.starts_with(&[0xff, 0x4f]) {
            return None;
        }
        (data, 0)
    };
    let size = match recovered {
        Some(info) => info.image_size,
        None => codestream::parse(stream, limits).ok()?.image_size,
    };
    if size.components == 0
        || u64::from(size.width) * u64::from(size.height) > 32_000_000 / u64::from(size.components)
    {
        return None;
    }
    for i in 0..size.components {
        let c = size.component(i).ok()?;
        if !(1..=31).contains(&c.precision) {
            return None;
        }
    }
    Some((size, color))
}

fn project_plane(size: &codestream::ImageSize, index: u16, x1: u32, y1: u32) -> Option<Plane> {
    plane_from_component(
        size.component(index).ok()?,
        size.x_origin,
        size.y_origin,
        x1,
        y1,
    )
}

fn plane_from_component(
    c: codestream::ComponentInfo,
    x0: u32,
    y0: u32,
    x1: u32,
    y1: u32,
) -> Option<Plane> {
    let dx = u32::from(c.x_subsampling);
    let dy = u32::from(c.y_subsampling);
    if dx == 0 || dy == 0 {
        return None;
    }
    Some(Plane {
        width: x1.div_ceil(dx) - x0.div_ceil(dx),
        height: y1.div_ceil(dy) - y0.div_ceil(dy),
        precision: c.precision.into(),
        signed: c.signed.into(),
        dx,
        dy,
        alpha: 0,
    })
}

fn project_header(
    size: &codestream::ImageSize,
    color: i32,
    index: u32,
    batch: bool,
) -> Option<(Header, Plane)> {
    project_header_with(size, color, index, batch, |index, x1, y1| {
        project_plane(size, index, x1, y1)
    })
}

fn project_header_with(
    size: &codestream::ImageSize,
    color: i32,
    index: u32,
    batch: bool,
    project: impl Fn(u16, u32, u32) -> Option<Plane>,
) -> Option<(Header, Plane)> {
    let index = u16::try_from(index).ok()?;
    let x1 = size.x_origin.checked_add(size.width)?;
    let y1 = size.y_origin.checked_add(size.height)?;
    let plane = project(index, x1, y1)?;
    let mut header = Header {
        x0: size.x_origin,
        y0: size.y_origin,
        x1,
        y1,
        count: size.components.into(),
        color,
        filled: 0,
        prefix: [Plane::default(); PREFIX_PLANES],
    };
    if batch && index == 0 {
        header.prefix[0] = plane;
        header.filled = 1;
        for (index, slot) in (1..size.components).zip(header.prefix[1..].iter_mut()) {
            let Some(next) = project(index, x1, y1) else {
                break; // Let the shim reach this index after its C allocations.
            };
            *slot = next;
            header.filled += 1;
        }
    }
    Some((header, plane))
}

#[unsafe(no_mangle)]
/// # Safety
/// `data` must point to `len` readable bytes. The output references must be
/// valid, exclusive, and disjoint from the input.
pub unsafe extern "C" fn jpeg2000_compat_inspect_v3(
    data: *const u8,
    len: usize,
    boxed: bool,
    strict: bool,
    index: u32,
    header: &mut Header,
    plane: &mut Plane,
) -> bool {
    let Some((size, color)) =
        (unsafe { input(data, len) }).and_then(|bytes| inspect(bytes, boxed, strict))
    else {
        return false;
    };
    let Some((projected, selected)) =
        project_header(&size, color, index, !COOPERATIVE_DEADLINES_ENABLED)
    else {
        return false;
    };
    *header = projected;
    *plane = selected;
    true
}

#[unsafe(no_mangle)]
/// # Safety
/// `data` must point to `len` readable bytes. A non-null result must be released
/// exactly once with `jpeg2000_compat_destroy_v3`.
pub unsafe extern "C" fn jpeg2000_compat_decode_v3(
    data: *const u8,
    len: usize,
    boxed: bool,
    indexed: bool,
    strict: bool,
    reduce: u8,
) -> *mut TypedImage {
    let Some(bytes) = (unsafe { input(data, len) }) else {
        return std::ptr::null_mut();
    };
    let Ok(limits) =
        jpeg2000_decoder::ResourceLimits::default().with_maximum_decoded_bytes(256 * 1024 * 1024)
    else {
        return std::ptr::null_mut();
    };
    let options = DecodeOptions::new(limits);
    let selection = DecodeSelection::default().with_discard_levels(reduce);
    let result = if boxed && indexed {
        let recovered =
            !strict && jpeg2000_decoder::inspect_pdf_compatible(bytes, &options).is_ok();
        if !strict && !recovered {
            return std::ptr::null_mut();
        }
        let Some(file) = parse_container(bytes, options.limits(), recovered) else {
            return std::ptr::null_mut();
        };
        file.codestream(0).and_then(|stream| {
            let stream = stream.data();
            if !recovered {
                jpeg2000_decoder::decode_codestream_selected(stream, &options, &selection)
            } else {
                jpeg2000_decoder::decode_pdf_compatible(stream, &options, &selection)
                    .map(|decoded| decoded.image)
            }
        })
    } else if !strict {
        jpeg2000_decoder::decode_pdf_compatible(bytes, &options, &selection)
            .map(|decoded| decoded.image)
    } else if boxed {
        jpeg2000_decoder::decode_jp2_selected(bytes, &options, &selection)
    } else {
        jpeg2000_decoder::decode_codestream_selected(bytes, &options, &selection)
    };
    result.map_or(std::ptr::null_mut(), |image| Box::into_raw(Box::new(image)))
}

#[unsafe(no_mangle)]
/// # Safety
/// `image` must be a live result of `jpeg2000_compat_decode_v3`; `plane` must be
/// a valid, exclusive output reference.
pub unsafe extern "C" fn jpeg2000_compat_plane_v3(
    image: &TypedImage,
    index: u32,
    plane: &mut Plane,
) -> bool {
    let Ok(index) = u16::try_from(index) else {
        return false;
    };
    let Ok(c) = image.component(index) else {
        return false;
    };
    let info = c.info();
    *plane = Plane {
        width: c.width(),
        height: c.height(),
        precision: info.precision.into(),
        signed: info.signed.into(),
        dx: info.x_subsampling.into(),
        dy: info.y_subsampling.into(),
        alpha: c
            .channel_definitions()
            .iter()
            .find_map(|definition| match definition.channel_type() {
                ChannelType::Opacity => Some(1),
                ChannelType::PremultipliedOpacity => Some(2),
                _ => None,
            })
            .unwrap_or(0),
    };
    true
}

#[unsafe(no_mangle)]
/// # Safety
/// `image` must be a live result of `jpeg2000_compat_decode_v3`.
pub unsafe extern "C" fn jpeg2000_compat_component_count_v3(image: &TypedImage) -> usize {
    image.components().len()
}

#[unsafe(no_mangle)]
/// # Safety
/// `image` must be a live decoded image and `plane` a valid reference. `dest`
/// must point to `len` writable `i32` values, disjoint from the image and plane.
pub unsafe extern "C" fn jpeg2000_compat_copy_plane_v3(
    image: &TypedImage,
    index: u32,
    dest: *mut i32,
    len: usize,
    plane: &Plane,
) -> bool {
    let Ok(index) = u16::try_from(index) else {
        return false;
    };
    let Ok(c) = image.component(index) else {
        return false;
    };
    if c.width() != plane.width
        || c.height() != plane.height
        || u32::from(c.info().precision) != plane.precision
        || u32::from(c.info().signed) != plane.signed
    {
        return false;
    }
    let signed = match c.samples() {
        TypedSamples::Signed(s) => s.len(),
        TypedSamples::Unsigned(s) => s.len(),
    };
    if dest.is_null() || len != signed {
        return false;
    }
    // The C adapter allocates exactly len samples for this call.
    let out = unsafe { std::slice::from_raw_parts_mut(dest, len) };
    match c.samples() {
        TypedSamples::Signed(s) => out
            .iter_mut()
            .zip(s)
            .all(|(dst, &src)| i32::try_from(src).map(|v| *dst = v).is_ok()),
        TypedSamples::Unsigned(s) => out
            .iter_mut()
            .zip(s)
            .all(|(dst, &src)| i32::try_from(src).map(|v| *dst = v).is_ok()),
    }
}

#[unsafe(no_mangle)]
/// # Safety
/// `image` must be null or an unconsumed result of `jpeg2000_compat_decode_v3`,
/// with no outstanding references.
pub unsafe extern "C" fn jpeg2000_compat_destroy_v3(image: *mut TypedImage) {
    if !image.is_null() {
        drop(unsafe { Box::from_raw(image) });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn size(components: u16) -> codestream::ImageSize {
        let mut data =
            include_bytes!("../../../validation/generated/corpus/raw-minimal.j2k").to_vec();
        // Extend SIZ's component table without changing the packet payload:
        // these tests exercise header inspection, not entropy decode.
        data[40..42].copy_from_slice(&components.to_be_bytes());
        data[4..6].copy_from_slice(&(38 + 3 * components).to_be_bytes());
        data.splice(45..45, (1..components).flat_map(|i| [7, 1 + i as u8, 1]));
        inspect(&data, false, true).unwrap().0
    }

    fn fields(p: Plane) -> [u32; 7] {
        [
            p.width,
            p.height,
            p.precision,
            p.signed,
            p.dx,
            p.dy,
            p.alpha,
        ]
    }

    #[test]
    fn leading_prefix_matches_per_index_projection() {
        for count in [1, 3, 4, 5] {
            let size = size(count);
            let (header, first) = project_header(&size, 17, 0, true).unwrap();
            assert_eq!(header.filled, u32::from(count.min(4)));
            assert_eq!((header.count, header.color), (u32::from(count), 17));
            assert_eq!(fields(first), fields(header.prefix[0]));
            for i in 0..header.count {
                let (single, plane) = project_header(&size, 17, i, false).unwrap();
                assert_eq!(single.filled, 0);
                assert_eq!(plane.dx, i + 1);
                if i < header.filled {
                    assert_eq!(fields(header.prefix[i as usize]), fields(plane));
                }
            }
        }
    }

    #[test]
    fn invalid_index_and_endpoint_overflow_refuse_projection() {
        let mut size = size(1);
        assert!(project_header(&size, 0, 1, true).is_none());
        assert!(project_header(&size, 0, 1 << 16, true).is_none());
        size.x_origin = u32::MAX;
        assert!(project_header(&size, 0, 0, true).is_none());
    }

    #[test]
    fn later_zero_sampling_stops_prefix_without_failing_plane_zero() {
        let size = size(4);
        let project = |index, x1, y1| {
            let mut component = size.component(index).ok()?;
            if index == 2 {
                component.x_subsampling = 0;
            }
            plane_from_component(component, size.x_origin, size.y_origin, x1, y1)
        };
        let (header, first) = project_header_with(&size, 0, 0, true, project).unwrap();
        assert_eq!(header.filled, 2);
        assert_eq!(fields(header.prefix[0]), fields(first));
        assert!(project_header_with(&size, 0, 2, false, project).is_none());
        assert!(project_header_with(&size, 0, 3, false, project).is_some());
    }
}
