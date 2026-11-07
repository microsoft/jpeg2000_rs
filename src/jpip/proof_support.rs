#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn databin_id_view(value: DatabinId) -> crate::specs::Part2JpipDatabin {
        (value.class_identifier, value.class, value.codestream, value.in_class)
    }

    pub open spec fn databin_id_outcome(value: Result<DatabinId, DecodeError>)
        -> Result<crate::specs::Part2JpipDatabin, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(databin_id_view(value)) }
    }

    pub closed spec fn jpip_context_view(value: JpipHeaderContext) -> crate::specs::Part2JpipContext {
        (value.previous_class, value.previous_codestream)
    }

    pub closed spec fn jpip_parser_context(value: &JpipMessageParser) -> crate::specs::Part2JpipContext {
        jpip_context_view(value.context)
    }

    pub closed spec fn jpip_parser_limits(value: &JpipMessageParser) -> &ResourceLimits {
        &value.limits
    }

    pub open spec fn jpip_parser_view(value: &JpipMessageParser)
        -> (crate::specs::Part2JpipContext, ResourceLimits) {
        (jpip_parser_context(value), *jpip_parser_limits(value))
    }

    proof fn jpip_context_fields(value: JpipHeaderContext)
        ensures jpip_context_view(value) == (value.previous_class, value.previous_codestream),
    {
        reveal(jpip_context_view);
    }

    proof fn jpip_parser_fields(value: &JpipMessageParser)
        ensures jpip_parser_context(value) == jpip_context_view(value.context),
            jpip_parser_limits(value) == &value.limits,
    {
        reveal(jpip_parser_context);
        reveal(jpip_parser_limits);
    }

    pub closed spec fn jpip_header_view(value: JpipMessageHeader) -> crate::specs::Part2JpipHeader {
        (databin_id_view(value.databin), value.offset, value.length, value.last_byte, value.auxiliary, value.header_length)
    }

    pub closed spec fn jpip_eor_view(value: &JpipEndOfResponse) -> (u8, Seq<u8>, usize) {
        (value.reason_code, value.body@, value.header_length)
    }

    pub closed spec fn jpip_eor_body_reference<'a>(value: &JpipEndOfResponse<'a>) -> &'a [u8] {
        value.body
    }

    pub closed spec fn jpip_message_view(value: JpipMessage) -> crate::specs::Part2JpipMessage {
        match value {
            JpipMessage::Data { header, body } => crate::specs::Part2JpipMessage::Data { header: jpip_header_view(header), body: body@ },
            JpipMessage::EndOfResponse(value) => crate::specs::Part2JpipMessage::EndOfResponse {
                reason: value.reason_code, body: value.body@, header_length: value.header_length,
            },
        }
    }

    pub open spec fn jpip_message_outcome(value: Result<(JpipMessage, usize), DecodeError>) -> crate::specs::Part2JpipParsed {
        match value { Err(error) => Err(error), Ok(value) => Ok((jpip_message_view(value.0), value.1)) }
    }

    pub closed spec fn jpip_message_body_reference<'a>(value: &JpipMessage<'a>) -> &'a [u8] {
        match value { JpipMessage::Data { body, .. } => *body, JpipMessage::EndOfResponse(end) => end.body }
    }

    proof fn jpip_message_values_known(value: JpipMessage)
        ensures jpip_message_view(value) == match value {
            JpipMessage::Data { header, body } => crate::specs::Part2JpipMessage::Data {
                header: jpip_header_view(header), body: body@,
            },
            JpipMessage::EndOfResponse(end) => crate::specs::Part2JpipMessage::EndOfResponse {
                reason: end.reason_code, body: end.body@, header_length: end.header_length,
            },
        },
    {
        reveal(jpip_message_view);
    }

    proof fn jpip_header_fields(value: JpipMessageHeader)
        ensures jpip_header_view(value) == (databin_id_view(value.databin), value.offset, value.length,
            value.last_byte, value.auxiliary, value.header_length),
    {
        reveal(jpip_header_view);
    }
}
