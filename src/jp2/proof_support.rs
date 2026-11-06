#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn box_type_from_bytes_model(bytes: [u8; 4]) -> BoxType {
        BoxType(crate::specs::part2_box_u32(bytes))
    }

    pub closed spec fn box_reader_state(reader: &BoxReader) -> crate::specs::Part2BoxReaderState {
        crate::specs::Part2BoxReaderState {
            input: reader.input@, limits: reader.limits, position: reader.position,
            metadata_bytes: reader.metadata_bytes, work_units: reader.work_units, failed: reader.failed,
        }
    }

    pub closed spec fn box_reader_input_reference<'a>(reader: &BoxReader<'a>) -> &'a [u8] {
        reader.input
    }

    pub closed spec fn box_header_view(header: BoxHeader) -> crate::specs::Part2BoxHeader {
        (header.box_type, header.offset, header.header_length, header.total_length)
    }

    pub open spec fn box_reference_view(value: BoxRef) -> crate::specs::Part2BoxReference {
        (box_header_view(value.header), value.payload@)
    }

    pub open spec fn box_read_outcome(result: Result<Option<BoxRef>, DecodeError>)
        -> Result<Option<crate::specs::Part2BoxReference>, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(None) => Ok(None), Ok(Some(value)) => Ok(Some(box_reference_view(value))) }
    }

    pub open spec fn required_box_outcome(result: Result<BoxRef, DecodeError>)
        -> Result<crate::specs::Part2BoxReference, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(box_reference_view(value)) }
    }

    pub open spec fn box_ref_outcome(result: Option<Result<BoxRef, DecodeError>>)
        -> Option<Result<crate::specs::Part2BoxReference, DecodeError>>
    {
        match result { None => None, Some(Err(error)) => Some(Err(error)), Some(Ok(value)) => Some(Ok(box_reference_view(value))) }
    }

    pub open spec fn box_reader_outcome(result: Result<BoxReader, DecodeError>)
        -> Result<crate::specs::Part2BoxReaderState, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(reader) => Ok(box_reader_state(&reader)) }
    }

    pub open spec fn source_opacity_value_view(value: &LayerOpacity) -> crate::specs::Part2SourceOpacity {
        match value {
            LayerOpacity::Straight => crate::specs::Part2SourceOpacity::Straight,
            LayerOpacity::Premultiplied => crate::specs::Part2SourceOpacity::Premultiplied,
            LayerOpacity::ChromaKey { channels, values } =>
                crate::specs::Part2SourceOpacity::ChromaKey { channels: *channels, values: values@ },
        }
    }

    pub open spec fn source_opacity_reference_view(value: Option<&LayerOpacity>)
        -> Option<crate::specs::Part2SourceOpacity>
    {
        match value { None => None, Some(value) => Some(source_opacity_value_view(value)) }
    }

    pub closed spec fn source_layer_opacity(layer: &CompositingLayer)
        -> Option<crate::specs::Part2SourceOpacity>
    {
        match &layer.opacity { None => None, Some(opacity) => Some(source_opacity_value_view(opacity)) }
    }

    pub closed spec fn source_layer_geometry(layer: &CompositingLayer) -> (u64, u16, u16) {
        (layer.header.offset, layer.horizontal_grid_size, layer.vertical_grid_size)
    }

    pub closed spec fn source_layer_nested_metadata(layer: &CompositingLayer) -> u32 {
        layer.nested_metadata_boxes
    }

    pub closed spec fn source_file_metadata(file: &Jp2File) -> (u32, u32) {
        (file.metadata_boxes, file.metadata_depth)
    }

    pub closed spec fn source_file_composition_reference<'file>(
        file: &'file Jp2File<'_>,
    ) -> Option<&'file Composition> {
        match &file.composition { None => None, Some(composition) => Some(composition) }
    }

    pub closed spec fn source_layer_registrations(layer: &CompositingLayer) -> Seq<CodestreamRegistration> {
        layer.registrations@
    }

    pub closed spec fn source_layer_color_group(layer: &CompositingLayer) -> Seq<ColorSpecification> {
        layer.color_group@
    }

    pub open spec fn source_layer_color_override(layer: &CompositingLayer) -> Option<ColorMethod> {
        let colors = source_layer_color_group(layer);
        if colors.len() == 0 { None } else { Some(color_specification_method(&colors[0])) }
    }

    pub closed spec fn source_file_layers<'input>(file: &Jp2File<'input>) -> Seq<CompositingLayer<'input>> {
        file.compositing_layers@
    }

    pub open spec fn source_layer_routing_config(
        file: &Jp2File, layer: &CompositingLayer,
    ) -> crate::specs::Part2LayerRoutingConfig {
        (general_layer_config(file, layer), source_layer_color_override(layer), source_layer_geometry(layer))
    }

    pub open spec fn source_file_layer_configs(file: &Jp2File) -> Seq<crate::specs::Part2LayerRoutingConfig> {
        let layers = source_file_layers(file);
        Seq::new(layers.len(), |i: int| source_layer_routing_config(file, &layers[i]))
    }

    pub closed spec fn jpx_file_layer_reference<'file, 'input>(
        file: &'file Jp2File<'input>, index: usize,
    ) -> Option<&'file CompositingLayer<'input>> {
        if index < file.compositing_layers@.len() {
            Some(&file.compositing_layers@[index as int])
        } else { None }
    }

    pub(crate) proof fn source_layer_reference_known(file: &Jp2File, index: usize)
        ensures jpx_file_layer_reference(file, index) == if index < source_file_layers(file).len() {
            Some(&source_file_layers(file)[index as int])
        } else { None },
    {
    }

    pub closed spec fn source_layer_definition_records(layer: &CompositingLayer) -> Seq<ChannelDefinitionRecord> {
        layer.channel_definition_records@
    }

    pub open spec fn general_layer_config(file: &Jp2File, layer: &CompositingLayer) -> crate::specs::Part2GeneralLayerConfig {
        let colors = source_layer_color_group(layer);
        let records = source_layer_definition_records(layer);
        crate::specs::Part2GeneralLayerConfig {
            color: if colors.len() == 0 { jpx_file_decode_view(file).2.2 }
                else { color_specification_method(&colors[0]) },
            horizontal_grid: source_layer_geometry(layer).1,
            vertical_grid: source_layer_geometry(layer).2,
            registrations: source_layer_registrations(layer),
            definitions: Seq::new(records.len(), |i: int|
                (records[i].channel, crate::image::channel_definition_view(records[i].definition))),
            opacity: source_layer_opacity(layer),
        }
    }

    pub(crate) proof fn source_opacity_known(value: &LayerOpacity)
        ensures source_opacity_value_view(value) == match value {
            LayerOpacity::Straight => crate::specs::Part2SourceOpacity::Straight,
            LayerOpacity::Premultiplied => crate::specs::Part2SourceOpacity::Premultiplied,
            LayerOpacity::ChromaKey { channels, values } =>
                crate::specs::Part2SourceOpacity::ChromaKey { channels: *channels, values: values@ },
        },
    {
    }

    pub closed spec fn source_association_header_view(association: &CodestreamHeaderAssociation)
        -> (u64, Option<crate::specs::Part2AssociatedHeader>)
    {
        (association.header.offset, match &association.parsed {
            None => None, Some(header) => Some(associated_header_view(header)),
        })
    }

    pub open spec fn source_optional_association_view(association: Option<&CodestreamHeaderAssociation>)
        -> Option<(u64, Option<crate::specs::Part2AssociatedHeader>)>
    {
        match association { None => None, Some(association) => Some(source_association_header_view(association)) }
    }

    pub closed spec fn file_type_view(file_type: &FileType) -> crate::specs::Part2FileType {
        (file_type.brand, file_type.minor_version, file_type.compatible_brands@)
    }

    pub open spec fn file_type_outcome(result: Result<FileType, DecodeError>)
        -> Result<crate::specs::Part2FileType, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(value) => Ok(file_type_view(&value)) }
    }

    pub open spec fn container_prefix_relation(
        result: Result<Jp2File, DecodeError>,
        prefix: Result<(crate::specs::Part2FileType, crate::specs::Part2BoxReaderState), DecodeError>,
    ) -> bool {
        match prefix {
            Err(error) => match result { Err(actual) => actual == error, Ok(_) => false },
            Ok(value) => match result { Err(_) => true, Ok(file) => jpx_file_decode_view(&file).0 == value.0 },
        }
    }

    pub closed spec fn box_header_offset(header: BoxHeader) -> u64 {
        header.offset
    }

    pub closed spec fn codestream_source_view(stream: &CodestreamBox) -> crate::specs::Part2CodestreamSource {
        (stream.data@, stream.header.offset, codestream_header_association_view(stream))
    }

    pub(crate) proof fn codestream_source_known_fields(stream: &CodestreamBox)
        ensures codestream_source_view(stream).2 == codestream_header_association_view(stream),
    {
    }

    pub closed spec fn jpx_file_decode_view(file: &Jp2File) -> crate::specs::Part2JpxDecodeInput {
        (file_type_view(&file.file_type),
            file.codestreams@.map_values(|stream: CodestreamBox| codestream_source_view(&stream)),
            associated_header_view(&file.header))
    }

    pub closed spec fn jpx_file_codestream_reference<'file, 'input>(
        file: &'file Jp2File<'input>, index: usize,
    ) -> Option<&'file CodestreamBox<'input>> {
        if index < file.codestreams@.len() {
            Some(&file.codestreams@[index as int])
        } else {
            None
        }
    }

    pub closed spec fn jpx_file_header_reference<'file>(file: &'file Jp2File<'_>) -> &'file Jp2Header {
        &file.header
    }

    pub closed spec fn associated_header_reference<'file>(
        selected: &'file CodestreamBox<'_>, fallback: &'file Jp2Header,
    ) -> Result<&'file Jp2Header, DecodeError> {
        match &selected.codestream_header {
            None => Ok(fallback),
            Some(association) => match &association.parsed {
                Some(header) => Ok(header),
                None => Err(DecodeError::MalformedInput {
                    offset: association.header.offset, kind: MalformedKind::MissingRequiredStructure,
                }),
            },
        }
    }

    pub closed spec fn jpx_file_associated_header_reference<'file>(
        file: &'file Jp2File<'_>, index: usize,
    ) -> Option<&'file Jp2Header> {
        match jpx_file_codestream_reference(file, index) {
            None => None,
            Some(selected) => match associated_header_reference(selected, jpx_file_header_reference(file)) {
                Err(_) => None,
                Ok(header) => Some(header),
            },
        }
    }

    pub(crate) proof fn jpx_file_associated_header_reference_unfold(file: &Jp2File, index: usize)
        ensures jpx_file_associated_header_reference(file, index)
            == match jpx_file_codestream_reference(file, index) {
                None => None,
                Some(selected) => match associated_header_reference(selected, jpx_file_header_reference(file)) {
                    Err(_) => None,
                    Ok(header) => Some(header),
                },
            },
    {
    }

    pub closed spec fn color_specification_method(color: &ColorSpecification) -> ColorMethod {
        color.method
    }

    pub open spec fn optional_color_specification_method(color: Option<&ColorSpecification>) -> Option<ColorMethod> {
        match color { None => None, Some(color) => Some(color_specification_method(color)) }
    }
}


#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn associated_header_view(header: &Jp2Header) -> crate::specs::Part2AssociatedHeader {
        (output_header_view(header), header.image, color_specification_method(&header.color))
    }

    pub closed spec fn codestream_header_association_view(stream: &CodestreamBox)
        -> Option<(u64, Option<crate::specs::Part2AssociatedHeader>)>
    {
        match &stream.codestream_header {
            None => None,
            Some(association) => Some((association.header.offset,
                match &association.parsed { None => None, Some(header) => Some(associated_header_view(header)) })),
        }
    }

    pub open spec fn associated_header_outcome(result: Result<&Jp2Header, DecodeError>)
        -> Result<crate::specs::Part2AssociatedHeader, DecodeError>
    {
        match result { Err(error) => Err(error), Ok(header) => Ok(associated_header_view(header)) }
    }

    pub open spec fn associated_header_option(header: Option<&Jp2Header>) -> Option<crate::specs::Part2AssociatedHeader> {
        match header { None => None, Some(header) => Some(associated_header_view(header)) }
    }
}


#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn palette_view(palette: &Palette) -> crate::specs::Part2PaletteModel {
        (palette.entries, palette.columns@, palette.values@)
    }

    pub open spec fn output_header_view(header: &Jp2Header) -> crate::specs::Part2OutputHeader {
        (
            match &header.palette { Some(palette) => Some(palette_view(palette)), None => None },
            Seq::new(header.component_mappings@.len(), |i: int|
                (header.component_mappings@[i].component, header.component_mappings@[i].mapping_type)),
            Seq::new(header.channel_definition_records@.len(), |i: int|
                (header.channel_definition_records@[i].channel,
                    crate::image::channel_definition_view(header.channel_definition_records@[i].definition))),
        )
    }
}
