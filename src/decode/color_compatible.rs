use crate::color::{CompatibleColorImage, convert_jp2_color_compatible};
use crate::{DecodeError, DecodeOptions, jp2};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Decode JP2 with explicit, observable eight-bit EnumCS20 RGB passthrough.
///
/// The native decode remains unchanged; its mapped image is passed to the
/// compatible color converter. Container metadata is parsed again after native
/// decoding. Both passes enforce the supplied limits and report their failures.
/// Normal strict color APIs never opt into this interpretation.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::compatible_decode_result(input@,crate::options::decode_options_limits(options),
        crate::color::compatible_color_outcome(result)),
    result != Err(DecodeError::AllocationFailed) ==> crate::color::compatible_color_outcome(result)
        == crate::specs::compatible_decode_value(input@,crate::options::decode_options_limits(options)),
))]
pub fn decode_jp2_color_compatible(
    input: &[u8],
    options: &DecodeOptions,
) -> Result<CompatibleColorImage, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::compatible_decode_value_unfold(input@,crate::options::decode_options_limits(options));
    }
    let decoded = super::api::decode_jp2(input, options);
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=decoded {
            crate::specs::compatible_decode_actual(input@,crate::options::decode_options_limits(options),
                Err(error),Err(error));
        }
    }
    let image = decoded?;
    let parsed = jp2::parse(input, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=parsed {
            crate::specs::compatible_after_native_actual(input@,crate::options::decode_options_limits(options),
                crate::image::typed_image_value_view(image),Err(error),Err(error));
            crate::specs::compatible_decode_actual(input@,crate::options::decode_options_limits(options),
                Ok(crate::image::typed_image_value_view(image)),Err(error));
        }
    }
    let file = parsed?;
    let header = file.header();
    #[cfg(verus_keep_ghost)]
    proof! { jp2::raw_render_header_known(header); }
    let passthrough = crate::color::esrgb8_compatible(&image, header.color.method());
    let profile = if passthrough {
        Ok(())
    } else {
        super::color_profile::validate_esrgb_color_display_profile(&file)
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Err(error)=profile {
            crate::specs::compatible_after_native_actual(input@,crate::options::decode_options_limits(options),
                crate::image::typed_image_value_view(image),Ok(jp2::raw_jp2_file_view(&file)),Err(error));
            crate::specs::compatible_decode_actual(input@,crate::options::decode_options_limits(options),
                Ok(crate::image::typed_image_value_view(image)),Err(error));
        }
    }
    profile?;
    let converted = convert_jp2_color_compatible(&image, &header.color, options.limits());
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::compatible_after_native_actual(input@,crate::options::decode_options_limits(options),
            crate::image::typed_image_value_view(image),Ok(jp2::raw_jp2_file_view(&file)),
            crate::color::compatible_color_outcome(converted));
        crate::specs::compatible_decode_actual(input@,crate::options::decode_options_limits(options),
            Ok(crate::image::typed_image_value_view(image)),crate::color::compatible_color_outcome(converted));
    }
    converted
}
