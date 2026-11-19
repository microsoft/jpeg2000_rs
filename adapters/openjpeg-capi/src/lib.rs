use jpeg2000_decoder::{
    DecodeError, DecodeOptions, DecodeSelection, MalformedKind, TypedImage, TypedSamples,
    codestream, jp2,
};

#[repr(C)]
pub struct Header {
    width: u32,
    height: u32,
    count: u32,
    color: i32,
}

#[repr(C)]
pub struct Plane {
    width: u32,
    height: u32,
    precision: u32,
    signed: u32,
    dx: u32,
    dy: u32,
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

fn inspect(
    data: &[u8],
    boxed: bool,
    indexed: bool,
    strict: bool,
) -> Option<(codestream::ImageSize, i32)> {
    let options = DecodeOptions::default();
    let limits = options.limits();
    let recovered = if strict {
        None
    } else {
        Some(jpeg2000_decoder::inspect_pdf_compatible(data, &options).ok()?)
    };
    let (stream, color) = if boxed {
        let file = parse_container(data, limits, recovered.is_some())?;
        if file.file_type().brand != jp2::BoxType::JP2_BRAND
            || file.codestream_count() != 1
            || (!indexed
                && (file.header.palette.is_some() || !file.header.component_mappings.is_empty()))
        {
            return None;
        }
        let color = match file.header.color.method {
            jp2::ColorMethod::Enumerated { color_space: 16 } => 1,
            jp2::ColorMethod::Enumerated { color_space: 17 } => 2,
            jp2::ColorMethod::Enumerated { color_space: 18 } => 3,
            jp2::ColorMethod::Enumerated { color_space: 12 } => 5,
            _ => return None,
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
    if size.x_origin != 0
        || size.y_origin != 0
        || size.components == 0
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

#[unsafe(no_mangle)]
pub unsafe extern "C" fn jpeg2000_compat_inspect(
    data: *const u8,
    len: usize,
    boxed: bool,
    indexed: bool,
    strict: bool,
    index: u32,
    header: &mut Header,
    plane: &mut Plane,
) -> bool {
    let Some((size, color)) =
        (unsafe { input(data, len) }).and_then(|bytes| inspect(bytes, boxed, indexed, strict))
    else {
        return false;
    };
    let Some(c) = u16::try_from(index)
        .ok()
        .and_then(|i| size.component(i).ok())
    else {
        return false;
    };
    *header = Header {
        width: size.width,
        height: size.height,
        count: size.components.into(),
        color,
    };
    *plane = Plane {
        width: size.width,
        height: size.height,
        precision: c.precision.into(),
        signed: c.signed.into(),
        dx: c.x_subsampling.into(),
        dy: c.y_subsampling.into(),
    };
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn jpeg2000_compat_decode(
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
pub unsafe extern "C" fn jpeg2000_compat_plane(
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
    };
    true
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn jpeg2000_compat_copy_plane(
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
pub unsafe extern "C" fn jpeg2000_compat_destroy(image: *mut TypedImage) {
    if !image.is_null() {
        drop(unsafe { Box::from_raw(image) });
    }
}
