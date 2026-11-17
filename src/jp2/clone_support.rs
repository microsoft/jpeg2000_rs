//! Shared executing metadata-clone producers used by native Clone and Verus.

use super::{CodestreamHeaderAssociation, ColorSpecification, Jp2Header, Palette};
use crate::DecodeError;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::full_color_specification_view(&result)
        == crate::specs::part2_color_specification_clone(super::full_color_specification_view(source)),
))]
pub(super) fn color_specification_clone(source: &ColorSpecification) -> ColorSpecification {
    ColorSpecification {
        method: Clone::clone(&source.method),
        precedence: Clone::clone(&source.precedence),
        approximation: Clone::clone(&source.approximation),
        icc_profile: Clone::clone(&source.icc_profile),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::palette_view(&result) == crate::specs::part2_owned_palette_clone(super::palette_view(source)),
))]
pub(super) fn palette_clone(source: &Palette) -> Palette {
    Palette {
        entries: Clone::clone(&source.entries),
        columns: Clone::clone(&source.columns),
        values: Clone::clone(&source.values),
    }
}

#[allow(
    clippy::manual_map,
    reason = "Explicit cases route the original optional-Palette clone through its checked native producer"
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::optional_palette_view(&result)
        == crate::specs::part2_optional_palette_clone(super::optional_palette_view(source)),
))]
pub(super) fn optional_palette_clone(source: &Option<Palette>) -> Option<Palette> {
    match source {
        None => None,
        Some(palette) => Some(palette_clone(palette)),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::raw_jp2_header_view(&result) == crate::specs::part2_jp2_header_clone(super::raw_jp2_header_view(source)),
))]
pub(super) fn jp2_header_clone(source: &Jp2Header) -> Jp2Header {
    Jp2Header {
        image: Clone::clone(&source.image),
        color: color_specification_clone(&source.color),
        nested_box_count: Clone::clone(&source.nested_box_count),
        palette_entries: Clone::clone(&source.palette_entries),
        palette_columns: Clone::clone(&source.palette_columns),
        component_mapping_entries: Clone::clone(&source.component_mapping_entries),
        channel_definitions: Clone::clone(&source.channel_definitions),
        palette: optional_palette_clone(&source.palette),
        component_mappings: Clone::clone(&source.component_mappings),
        channel_definition_records: Clone::clone(&source.channel_definition_records),
        capture_resolution: Clone::clone(&source.capture_resolution),
        display_resolution: Clone::clone(&source.display_resolution),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::storage_copy_result(source@,result),
))]
fn try_copy_header_values<T: Copy>(source: &[T]) -> Result<Vec<T>, DecodeError> {
    let mut values = if source.is_empty() {
        Vec::new()
    } else {
        crate::allocation::empty_with_capacity(source.len())?
    };
    let mut index = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= source.len(),
            values@ == source@.take(index as int),
        decreases source.len() - index,
    ))]
    while index < source.len() {
        values.push(source[index]);
        index += 1;
        #[cfg(verus_keep_ghost)]
        proof! { assert(values@ =~= source@.take(index as int)); }
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(values@ =~= source@); }
    Ok(values)
}

#[allow(
    clippy::manual_map,
    reason = "Explicit cases expose the original optional owners to the checked copy contracts"
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_header_clone_storage_result(super::raw_jp2_header_view(source),
        super::raw_jp2_header_outcome(result)),
        match result {
            Ok(header) => super::raw_jp2_header_view(&header) == super::raw_jp2_header_view(source),
            Err(error) => error == DecodeError::AllocationFailed,
        },
))]
pub(super) fn try_jp2_header_clone(source: &Jp2Header) -> Result<Jp2Header, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = super::raw_jp2_header_view(source);
        let ghost icc_source = match original.color.3 { None => Seq::empty(), Some(bytes) => bytes };
        let ghost columns_source = match original.palette { None => Seq::empty(), Some(palette) => palette.1 };
        let ghost values_source = match original.palette { None => Seq::empty(), Some(palette) => palette.2 };
    }
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_prefix_normal(original,0); }
    let icc = match &source.color.icc_profile {
        None => Ok(Vec::new()),
        Some(bytes) => try_copy_header_values(bytes),
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_copied(original,0,icc_source,icc); }
    let icc = icc?;
    let columns = match &source.palette {
        None => Ok(Vec::new()),
        Some(palette) => try_copy_header_values(&palette.columns),
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_copied(original,1,columns_source,columns); }
    let columns = columns?;
    let values = match &source.palette {
        None => Ok(Vec::new()),
        Some(palette) => try_copy_header_values(&palette.values),
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_copied(original,2,values_source,values); }
    let values = values?;
    let mappings = try_copy_header_values(&source.component_mappings);
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_copied(original,3,source.component_mappings@,mappings); }
    let mappings = mappings?;
    let definitions = try_copy_header_values(&source.channel_definition_records);
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_copied(original,4,source.channel_definition_records@,definitions); }
    let definitions = definitions?;
    let icc_profile = match &source.color.icc_profile {
        None => None,
        Some(_) => Some(icc),
    };
    let palette = match &source.palette {
        None => None,
        Some(palette) => Some(Palette {
            entries: palette.entries,
            columns,
            values,
        }),
    };
    #[cfg(verus_keep_ghost)]
    proof! { crate::specs::part2_header_clone_success(original); }
    Ok(Jp2Header {
        image: Clone::clone(&source.image),
        color: ColorSpecification {
            method: Clone::clone(&source.color.method),
            precedence: Clone::clone(&source.color.precedence),
            approximation: Clone::clone(&source.color.approximation),
            icc_profile,
        },
        nested_box_count: Clone::clone(&source.nested_box_count),
        palette_entries: Clone::clone(&source.palette_entries),
        palette_columns: Clone::clone(&source.palette_columns),
        component_mapping_entries: Clone::clone(&source.component_mapping_entries),
        channel_definitions: Clone::clone(&source.channel_definitions),
        palette,
        component_mappings: mappings,
        channel_definition_records: definitions,
        capture_resolution: Clone::clone(&source.capture_resolution),
        display_resolution: Clone::clone(&source.display_resolution),
    })
}

#[allow(
    clippy::manual_map,
    reason = "Explicit cases route the original optional header clone through its checked native producer"
)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::optional_jp2_header_view(&result)
        == crate::specs::part2_optional_jp2_header_clone(super::optional_jp2_header_view(source)),
))]
pub(super) fn optional_jp2_header_clone(source: &Option<Jp2Header>) -> Option<Jp2Header> {
    match source {
        None => None,
        Some(header) => Some(jp2_header_clone(header)),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures super::raw_codestream_association_view(&result)
        == crate::specs::part2_codestream_association_clone(super::raw_codestream_association_view(source)),
        super::raw_codestream_association_payload_reference(&result)
            == super::raw_codestream_association_payload_reference(source),
))]
pub(super) fn codestream_association_clone<'a>(
    source: &CodestreamHeaderAssociation<'a>,
) -> CodestreamHeaderAssociation<'a> {
    CodestreamHeaderAssociation {
        header: Clone::clone(&source.header),
        payload: Clone::clone(&source.payload),
        parsed: optional_jp2_header_clone(&source.parsed),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part2_association_clone_storage_result(
        super::raw_codestream_association_view(source),super::raw_codestream_association_outcome(result)),
        match result {
            Ok(association) => super::raw_codestream_association_view(&association)
                    == super::raw_codestream_association_view(source)
                && super::raw_codestream_association_payload_reference(&association)
                    == super::raw_codestream_association_payload_reference(source),
            Err(error) => error == DecodeError::AllocationFailed,
        },
))]
pub(super) fn try_codestream_association_clone<'a>(
    source: &CodestreamHeaderAssociation<'a>,
) -> Result<CodestreamHeaderAssociation<'a>, DecodeError> {
    let parsed = match &source.parsed {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_association_clone_storage_normal(
                    super::raw_codestream_association_view(source));
            }
            None
        }
        Some(header) => {
            let cloned = try_jp2_header_clone(header);
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::specs::part2_association_clone_from_header(
                    super::raw_codestream_association_view(source),super::raw_jp2_header_outcome(cloned));
            }
            Some(cloned?)
        }
    };
    Ok(CodestreamHeaderAssociation {
        header: Clone::clone(&source.header),
        payload: Clone::clone(&source.payload),
        parsed,
    })
}
