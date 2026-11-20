use crate::{DecodeError, UnsupportedColorConversion, jp2};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part2_esrgb_color_display_profile(jp2::raw_jp2_file_view(file)),
))]
pub(super) fn validate_esrgb_color_display_profile(
    file: &jp2::Jp2File<'_>,
) -> Result<(), DecodeError> {
    let header = file.header();
    #[cfg(verus_keep_ghost)]
    proof! {
        jp2::raw_render_file_known(file);
        jp2::raw_render_header_known(header);
    }
    if matches!(
        header.color.method(),
        jp2::ColorMethod::Enumerated { color_space: 20 }
    ) && !file.file_type().is_compatible_with(jp2::BoxType::JPX_BRAND)
    {
        return Err(DecodeError::UnsupportedColorConversion {
            reason: UnsupportedColorConversion::EnumeratedColorSpace,
        });
    }
    Ok(())
}
