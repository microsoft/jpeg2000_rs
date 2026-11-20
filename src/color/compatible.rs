use super::{ConvertedImage, conversion::convert_jp2_color};
use crate::image::TypedImage;
use crate::jp2::{ColorMethod, ColorSpecification, ENUMERATED_SRGB};
use crate::{DecodeError, ResourceLimits};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Assumptions made only by the explicit compatible color API.
#[derive(Clone, Copy, Default)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct ColorRecovery {
    /// Full-resolution unsigned 8-bit EnumCS20 samples were treated as ordinary RGB.
    /// This is OpenJPEG-compatible passthrough, not PIMA e-sRGB conversion.
    pub assumed_srgb_for_8bit_esrgb: bool,
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub struct CompatibleColorImage {
    pub image: ConvertedImage,
    pub recovery: ColorRecovery,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn compatible_color_outcome(result: Result<CompatibleColorImage, DecodeError>)
        -> Result<(crate::specs::Part2ConvertedImage, ColorRecovery), DecodeError> {
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok((super::converted_image_model(&value.image), value.recovery)),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::color_esrgb8_compatible(
        crate::image::typed_image_value_view(*image), method),
))]
pub(crate) fn esrgb8_compatible(image: &TypedImage, method: ColorMethod) -> bool {
    let components = image.components();
    if !matches!(method, ColorMethod::Enumerated { color_space: 20 }) || components.len() != 3 {
        return false;
    }
    let width = image.width();
    let height = image.height();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::image::typed_image_value_view);
        reveal(crate::image::typed_image_component_views);
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant components.len() == 3, index <= components.len(),
            components@ == crate::image::typed_image_components(image),
            width == crate::image::typed_image_geometry(image).0,
            height == crate::image::typed_image_geometry(image).1,
            method == (ColorMethod::Enumerated {color_space:20}),
            forall|i: int| 0 <= i < index ==> {
                let c = #[trigger] crate::image::typed_image_component_views(image)[i];
                c.info.precision == 8 && !c.info.signed && c.info.x_subsampling == 1
                    && c.info.y_subsampling == 1 && c.info.x_registration == 0 && c.info.y_registration == 0
                    && c.width == width && c.height == height
            },
        decreases components.len() - index,
    ))]
    while index < components.len() {
        let component = &components[index];
        let info = component.info();
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::image::typed_image_component_views(image)[index as int]
                == crate::image::typed_component_view(component));
        }
        if info.precision != 8
            || info.signed
            || info.x_subsampling != 1
            || info.y_subsampling != 1
            || info.x_registration != 0
            || info.y_registration != 0
            || component.width() != width
            || component.height() != height
        {
            return false;
        }
        index += 1;
    }
    true
}

/// Convert color with an explicit, reported OpenJPEG-compatible EnumCS20 escape.
///
/// Only three full-resolution, unregistered, unsigned eight-bit planes may use
/// the RGB-passthrough interpretation. Other inputs use the strict converter.
/// Samples are normalized to the ordinary sixteen-bit output representation;
/// no PIMA transfer or correction is claimed for the eight-bit declaration.
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::color_compatible_result(crate::specs::Part2ColorConvertContext {
        image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
        bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits),
    },compatible_color_outcome(result)),
    result!=Err(DecodeError::AllocationFailed) ==> compatible_color_outcome(result) == crate::specs::color_compatible_value(
        crate::specs::Part2ColorConvertContext {
            image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits) }),
))]
pub fn convert_jp2_color_compatible(
    image: &TypedImage,
    color: &ColorSpecification,
    limits: &ResourceLimits,
) -> Result<CompatibleColorImage, DecodeError> {
    let assumed = esrgb8_compatible(image, color.method());
    let interpreted = crate::jp2::enumerated_color_specification(ENUMERATED_SRGB);
    let effective = if assumed { &interpreted } else { color };
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::jp2::srgb_enumeration_value();
        assert(crate::jp2::color_specification_method(&interpreted) ==
            (ColorMethod::Enumerated {color_space:16}));
        assert(crate::jp2::color_specification_method(effective) ==
            crate::specs::color_compatible_context(crate::specs::Part2ColorConvertContext {
                image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
                bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits),
            }).method);
    }
    let converted = convert_jp2_color(image, effective, limits);
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::color_compatible_actual(crate::specs::Part2ColorConvertContext {
            image:crate::image::typed_image_value_view(*image),method:crate::jp2::color_specification_method(color),
            bytes:crate::limits::resource_decoded_bytes_limit(limits),work:crate::limits::resource_work_limit(limits),
        },super::converted_image_result(converted));
    }
    Ok(CompatibleColorImage {
        image: converted?,
        recovery: ColorRecovery {
            assumed_srgb_for_8bit_esrgb: assumed,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codestream::ComponentInfo;
    use crate::image::{TypedComponent, TypedSamples};

    fn image(precision: u8, registration: u16) -> TypedImage {
        let components = [[0, 127, 255], [64, 128, 192], [2, 129, 254]]
            .into_iter()
            .map(|values| {
                TypedComponent::from_parts(
                    3,
                    1,
                    ComponentInfo {
                        precision,
                        signed: false,
                        x_subsampling: 1,
                        y_subsampling: 1,
                        x_registration: registration,
                        y_registration: 0,
                    },
                    TypedSamples::Unsigned(values.to_vec()),
                )
            })
            .collect();
        TypedImage::from_components(3, 1, components, &ResourceLimits::default()).unwrap()
    }

    #[test]
    fn explicit_eight_bit_passthrough_matches_rgb_and_reports_assumption() {
        let image = image(8, 0);
        let limits = ResourceLimits::default();
        let esrgb = ColorSpecification::enumerated(20);
        assert!(convert_jp2_color(&image, &esrgb, &limits).is_err());
        let actual = convert_jp2_color_compatible(&image, &esrgb, &limits).unwrap();
        let rgb = ColorSpecification::enumerated(16);
        assert_eq!(
            actual.image,
            convert_jp2_color(&image, &rgb, &limits).unwrap()
        );
        assert!(actual.recovery.assumed_srgb_for_8bit_esrgb);
        let ordinary = convert_jp2_color_compatible(&image, &rgb, &limits).unwrap();
        assert_eq!(actual.image, ordinary.image);
        assert!(!ordinary.recovery.assumed_srgb_for_8bit_esrgb);
    }

    #[test]
    fn precision_and_registration_do_not_trigger_blanket_fallback() {
        let limits = ResourceLimits::default();
        let esrgb = ColorSpecification::enumerated(20);
        for input in [image(9, 0), image(8, 32768)] {
            assert!(convert_jp2_color_compatible(&input, &esrgb, &limits).is_err());
        }
        let input = image(10, 0);
        let actual = convert_jp2_color_compatible(&input, &esrgb, &limits).unwrap();
        assert_eq!(
            actual.image,
            convert_jp2_color(&input, &esrgb, &limits).unwrap()
        );
        assert!(!actual.recovery.assumed_srgb_for_8bit_esrgb);
    }

    #[test]
    fn compatible_conversion_preserves_output_limit_refusal() {
        let input = image(8, 0);
        let limits = ResourceLimits::default()
            .with_maximum_decoded_bytes(17)
            .unwrap();
        assert!(matches!(
            convert_jp2_color_compatible(&input, &ColorSpecification::enumerated(20), &limits),
            Err(DecodeError::LimitExceeded {
                resource: crate::Resource::DecodedBytes,
                limit: 17,
                actual: 18
            })
        ));
    }
}
