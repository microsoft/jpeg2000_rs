//! Binary message headers, inherited identifiers, and bounded response ingestion.

use super::{
    DatabinCache, DatabinClass, DatabinId, DecodeError, JpipEndOfResponse, JpipFragment,
    JpipHeaderContext, JpipMessage, JpipMessageHeader, JpipMessageParser, JpipResponseSummary,
    MAX_VBAS_BYTES, MalformedKind, Resource, ResourceLimits,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_outcome, databin_id_view, jpip_cache_fields, jpip_cache_view, jpip_context_fields,
    jpip_context_view, jpip_eor_body_reference, jpip_eor_view, jpip_header_fields,
    jpip_header_view, jpip_message_body_reference, jpip_message_outcome, jpip_message_values_known,
    jpip_message_view, jpip_parser_context, jpip_parser_fields, jpip_parser_limits,
    jpip_parser_view, jpip_response_outcome, jpip_response_summary_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(test)]
#[path = "message_result_tests.rs"]
mod result_tests;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl DatabinClass {
    const fn from_identifier(identifier: u64) -> Option<Self> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Option<Self>| {
            vstd::prelude::equal(result, crate::specs::part2_jpip_class(identifier))
        });
        if !crate::refinement::jpip_standard_class_assigned(identifier) {
            return None;
        }
        match identifier {
            0 | 1 => Some(Self::Precinct),
            2 => Some(Self::TileHeader),
            4 | 5 => Some(Self::TileData),
            6 => Some(Self::MainHeader),
            8 => Some(Self::Metadata),
            _ => None,
        }
    }

    pub const fn has_auxiliary(identifier: u64) -> bool {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: bool| {
            vstd::prelude::equal(result, crate::specs::part2_jpip_auxiliary(identifier))
        });
        crate::refinement::jpip_auxiliary_present(identifier)
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl DatabinId {
    pub(super) fn from_wire(
        class_identifier: u64,
        codestream: u64,
        in_class: u64,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                databin_id_outcome(result),
                crate::specs::part2_jpip_wire_databin(class_identifier, codestream, in_class),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        if matches!(class_identifier, 3 | 7) {
            Ok(Self {
                class_identifier,
                class: DatabinClass::Unassigned,
                codestream,
                in_class,
            })
        } else {
            Self::new(class_identifier, codestream, in_class)
        }
    }

    pub fn new(class_identifier: u64, codestream: u64, in_class: u64) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                databin_id_outcome(result),
                crate::specs::part2_jpip_databin(class_identifier, codestream, in_class),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        let class = DatabinClass::from_identifier(class_identifier)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_error(0, MalformedKind::InvalidJpipHeader),
                ))]
                || DecodeError::malformed(0, MalformedKind::InvalidJpipHeader),
            )?;
        Ok(Self {
            class_identifier,
            class,
            codestream,
            in_class,
        })
    }

    pub const fn class_identifier(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(result, databin_id_view(*self).0)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        self.class_identifier
    }

    pub const fn class(&self) -> DatabinClass {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: DatabinClass| {
            vstd::prelude::equal(result, databin_id_view(*self).1)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        self.class
    }

    pub const fn codestream(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(result, databin_id_view(*self).2)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        self.codestream
    }

    pub const fn in_class(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(result, databin_id_view(*self).3)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        self.in_class
    }

    pub(super) const fn same_as(&self, other: Self) -> bool {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: bool| {
            vstd::prelude::equal(
                result,
                crate::specs::part2_jpip_identity(databin_id_view(*self), databin_id_view(other)),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(databin_id_view); }
        crate::refinement::jpip_databin_identity(
            self.class_identifier,
            self.codestream,
            self.in_class,
            other.class_identifier,
            other.codestream,
            other.in_class,
        )
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipHeaderContext {
    pub const fn new() -> Self {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Self| jpip_context_view(result) == (None, None));
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_context_view); }
        Self {
            previous_class: None,
            previous_codestream: None,
        }
    }

    pub const fn previous_class(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Option<u64>| result == jpip_context_view(*self).0);
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_context_view); }
        self.previous_class
    }

    pub const fn previous_codestream(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Option<u64>| result == jpip_context_view(*self).1);
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_context_view); }
        self.previous_codestream
    }
}

impl JpipMessageHeader {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures databin_id_view(result) == jpip_header_view(*self).0,
    ))]
    pub const fn databin(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.databin
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_header_view(*self).1,))]
    pub const fn offset(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.offset
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_header_view(*self).2,))]
    pub const fn length(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.length
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_header_view(*self).3,))]
    pub const fn is_last_byte(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.last_byte
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_jpip_final_length(jpip_header_view(*self)),
    ))]
    pub const fn final_length(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        if self.last_byte {
            Some(self.offset.saturating_add(self.length))
        } else {
            None
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_header_view(*self).4,))]
    pub const fn auxiliary(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.auxiliary
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_header_view(*self).5,))]
    pub const fn header_length(&self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_header_fields(*self); }
        self.header_length
    }
}

impl<'a> JpipEndOfResponse<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_eor_view(self).0,))]
    pub const fn reason_code(&self) -> u8 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_eor_view); }
        self.reason_code
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == jpip_eor_body_reference(self),
            result@ == jpip_eor_view(self).1,
    ))]
    pub const fn body(&self) -> &'a [u8] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_eor_view); reveal(jpip_eor_body_reference); }
        self.body
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_eor_view(self).2,))]
    pub const fn header_length(&self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_eor_view); }
        self.header_length
    }
}

impl<'a> JpipMessage<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == jpip_message_body_reference(self),
    ))]
    pub const fn body(&self) -> &'a [u8] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_message_body_reference); }
        match self {
            Self::Data { body, .. } => body,
            Self::EndOfResponse(end) => end.body,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipMessageParser {
    pub const fn new(limits: ResourceLimits) -> Self {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Self| {
            vstd::prelude::equal(jpip_parser_context(&result), (None, None))
                && vstd::prelude::equal(*jpip_parser_limits(&result), limits)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_parser_context); reveal(jpip_parser_limits); reveal(jpip_context_view); }
        Self {
            context: JpipHeaderContext::new(),
            limits,
        }
    }
}

impl JpipMessageParser {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_context_view(result) == jpip_parser_context(self),
    ))]
    pub const fn context(&self) -> JpipHeaderContext {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_parser_fields(self); }
        self.context
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (jpip_message_outcome(result), jpip_parser_view(final(self)))
            == crate::specs::part2_jpip_parser_parse(input@, jpip_parser_view(old(self))),
    ))]
    pub fn parse<'a>(&mut self, input: &'a [u8]) -> Result<(JpipMessage<'a>, usize), DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_parser_fields(self); jpip_context_fields(self.context); }
        parse_jpip_message(input, &mut self.context, &self.limits)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (jpip_message_outcome(result), jpip_context_view(*final(context)))
        == crate::specs::part2_parse_jpip_message(input@, jpip_context_view(*old(context)), limits),
))]
pub fn parse_jpip_message<'a>(
    input: &'a [u8],
    context: &mut JpipHeaderContext,
    limits: &ResourceLimits,
) -> Result<(JpipMessage<'a>, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        jpip_context_fields(*context);
        reveal(jpip_message_view);
        reveal(jpip_header_view);
        crate::specs::part2_parse_jpip_message_unfold(input@, jpip_context_view(*context), limits);
    }
    if input.is_empty() {
        return Err(DecodeError::malformed(0, MalformedKind::Truncated));
    }
    if input.len() as u64 > limits.maximum_input_bytes() {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            limits.maximum_input_bytes(),
            input.len() as u64,
        ));
    }
    if input[0] == 0 {
        return parse_end_of_response(input);
    }

    let form = (input[0] >> 5) & 3;
    if !crate::refinement::jpip_header_form_valid(form) {
        return Err(DecodeError::malformed(0, MalformedKind::InvalidJpipHeader));
    }
    let last_byte = input[0] & 0x10 != 0;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost initial_context = jpip_context_view(*context); }
    let mut position = 0_usize;
    let in_class = read_vbas(input, &mut position, Some(0x0f))?;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost class_start = position; }

    let class_identifier = if crate::refinement::jpip_header_has_explicit_class(form) {
        read_vbas(input, &mut position, None)?
    } else {
        context.previous_class.unwrap_or(0)
    };
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost stream_start = position; }
    let codestream = if crate::refinement::jpip_header_has_explicit_codestream(form) {
        read_vbas(input, &mut position, None)?
    } else {
        context.previous_codestream.unwrap_or(0)
    };
    let databin = DatabinId::from_wire(class_identifier, codestream, in_class)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_jpip_data_identity_cut(input@, initial_context, limits,
            in_class, class_start, class_identifier, stream_start, codestream, position, databin_id_view(databin));
    }
    let parsed = parse_data_after_identity(input, position, databin, last_byte, limits)?;
    context.previous_class = Some(class_identifier);
    context.previous_codestream = Some(codestream);
    Ok(parsed)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures jpip_message_outcome(result) == crate::specs::part2_jpip_data_after_identity(
        input@, position, databin_id_view(databin), last_byte, limits),
        match result {
            Ok((JpipMessage::Data { header, .. }, _)) => databin_id_view(header.databin) == databin_id_view(databin),
            Ok(_) => false,
            Err(_) => true,
        },
))]
fn parse_data_after_identity<'a>(
    input: &'a [u8],
    mut position: usize,
    databin: DatabinId,
    last_byte: bool,
    limits: &ResourceLimits,
) -> Result<(JpipMessage<'a>, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::part2_jpip_data_after_identity);
        reveal(jpip_message_view);
        reveal(jpip_header_view);
        reveal(databin_id_view);
    }
    let offset = read_vbas(input, &mut position, None)?;
    let length = read_vbas(input, &mut position, None)?;
    let auxiliary = if DatabinClass::has_auxiliary(databin.class_identifier) {
        Some(read_vbas(input, &mut position, None)?)
    } else {
        None
    };
    let end = offset.checked_add(length).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
        ))]
        || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
    )?;
    if end > limits.maximum_input_bytes() {
        return Err(DecodeError::limit(
            Resource::InputBytes,
            limits.maximum_input_bytes(),
            end,
        ));
    }
    let body_length = usize::try_from(length)
        .map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
            ))]
            |_error| DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
        )?;
    let body_end = position.checked_add(body_length).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
        ))]
        || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
    )?;
    if body_end > input.len() {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::Truncated,
        ));
    }

    let header = JpipMessageHeader {
        databin,
        offset,
        length,
        last_byte,
        auxiliary,
        header_length: position,
    };
    Ok((
        JpipMessage::Data {
            header,
            body: &input[position..body_end],
        },
        body_end,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures jpip_message_outcome(result) == crate::specs::part2_jpip_eor(input@),
))]
fn parse_end_of_response(input: &[u8]) -> Result<(JpipMessage<'_>, usize), DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(jpip_message_view); }
    if input.len() < 2 {
        return Err(DecodeError::malformed(1, MalformedKind::Truncated));
    }
    let reason_code = input[1];
    let mut position = 2_usize;
    let length = read_vbas(input, &mut position, None)?;
    let body_length = usize::try_from(length)
        .map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
            ))]
            |_error| DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
        )?;
    let body_end = position.checked_add(body_length).ok_or_else(
        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
            ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
        ))]
        || DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow),
    )?;
    if crate::refinement::jpip_eor_extent(position, body_length) != body_end as u128 {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::ArithmeticOverflow,
        ));
    }
    if body_end > input.len() {
        return Err(DecodeError::malformed(
            position as u64,
            MalformedKind::Truncated,
        ));
    }
    Ok((
        JpipMessage::EndOfResponse(JpipEndOfResponse {
            reason_code,
            body: &input[position..body_end],
            header_length: position,
        }),
        body_end,
    ))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, *final(position)) == crate::specs::part2_jpip_read_vbas(input@, *old(position), first_mask),
))]
fn read_vbas(
    input: &[u8],
    position: &mut usize,
    first_mask: Option<u8>,
) -> Result<u64, DecodeError> {
    let start = *position;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_read_vbas); }
    let first = *input
        .get(*position)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(*position, MalformedKind::Truncated),
            ))]
            || DecodeError::malformed(*position as u64, MalformedKind::Truncated),
        )?;
    let mask = first_mask.unwrap_or(0x7f);
    let mut value = u64::from(first & mask);
    let mut byte = first;
    let mut count = 1_usize;
    *position = position
        .checked_add(1)
        .ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(start, MalformedKind::ArithmeticOverflow),
            ))]
            || DecodeError::malformed(start as u64, MalformedKind::ArithmeticOverflow),
        )?;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant 1 <= count,
                count <= MAX_VBAS_BYTES,
                start == *old(position),
                *position as nat == start as nat + count as nat,
                *position <= input.len(),
                crate::specs::part2_jpip_read_vbas(input@, start, first_mask)
                == crate::specs::part2_jpip_vbas_tail(input@, start, *position, value, byte, count),
            decreases MAX_VBAS_BYTES - count,
        )
    )]
    while byte & 0x80 != 0 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_vbas_tail); }
        if count >= MAX_VBAS_BYTES {
            return Err(DecodeError::malformed(
                start as u64,
                MalformedKind::InvalidJpipVbas,
            ));
        }
        byte = *input
            .get(*position)
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_error(*position, MalformedKind::Truncated),
                ))]
                || DecodeError::malformed(*position as u64, MalformedKind::Truncated),
            )?;
        let group = byte & 0x7f;
        let stepped = value
            .checked_mul(128)
            .and_then(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: (Option<u64>) =>
                    ensures result == if shifted as nat + group as nat > u64::MAX as nat { None }
                        else { Some((shifted as nat + group as nat) as u64) },
                ))]
                |shifted| shifted.checked_add(u64::from(group)),
            )
            .ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_error(start, MalformedKind::InvalidJpipVbas),
                ))]
                || DecodeError::malformed(start as u64, MalformedKind::InvalidJpipVbas),
            )?;
        if value > (u64::MAX - u64::from(group)) / 128
            || crate::refinement::jpip_vbas_step(value, group) != stepped
        {
            return Err(DecodeError::malformed(
                start as u64,
                MalformedKind::InvalidJpipVbas,
            ));
        }
        value = stepped;
        *position = position.checked_add(1).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(start, MalformedKind::ArithmeticOverflow),
            ))]
            || DecodeError::malformed(start as u64, MalformedKind::ArithmeticOverflow),
        )?;
        count += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_vbas_tail); }
    Ok(value)
}

impl JpipResponseSummary {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == jpip_response_summary_view(*self).0,
    ))]
    pub const fn messages(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_response_summary_view); }
        self.messages
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == jpip_response_summary_view(*self).1,
    ))]
    pub const fn end_of_response_reason(&self) -> Option<u8> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_response_summary_view); }
        self.end_of_response_reason
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (jpip_response_outcome(result), jpip_cache_view(final(cache)))
        == crate::specs::part2_ingest_jpip_response(input@, jpip_cache_view(old(cache))),
))]
pub fn ingest_jpip_response(
    input: &[u8],
    cache: &mut DatabinCache,
) -> Result<JpipResponseSummary, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        jpip_cache_fields(cache);
        reveal(jpip_response_summary_view);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost expected = crate::specs::part2_ingest_jpip_response(input@, jpip_cache_view(cache));
    }
    let mut parser = JpipMessageParser::new(cache.limits);
    let mut position = 0_usize;
    let mut messages = 0_u64;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant position <= input.len(),
                expected == crate::specs::part2_ingest_jpip_response(input@, jpip_cache_view(old(cache))),
                expected == crate::specs::part2_jpip_response_remaining(input@, jpip_cache_view(cache),
                    jpip_parser_context(&parser), *jpip_parser_limits(&parser), position, messages),
            decreases input.len() - position,
        )
    )]
    while position < input.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            jpip_cache_fields(cache);
            reveal(crate::specs::part2_jpip_response_remaining);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_cache = jpip_cache_view(cache);
        }
        let (message, consumed) = parser.parse(&input[position..])?;
        #[cfg(verus_keep_ghost)]
        proof! { jpip_message_values_known(message); }
        if consumed == 0 {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidJpipHeader,
            ));
        }
        match message {
            JpipMessage::Data { header, body } => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part2_jpip_response_data);
                    jpip_header_fields(header);
                }
                #[cfg(verus_keep_ghost)]
                proof_decl! {
                    let ghost data = crate::specs::part2_jpip_response_data(previous_cache,
                        jpip_header_view(header), body@, position, messages);
                }
                let fragment = JpipFragment::from_message(header, body, &cache.limits)?;
                cache.insert(fragment)?;
                messages = messages.checked_add(1).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
                    ))]
                    || {
                        DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
                    },
                )?;
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(data == (Ok(messages), jpip_cache_view(cache)));
                }
            }
            JpipMessage::EndOfResponse(end) => {
                let response_end = position.checked_add(consumed).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
                    ))]
                    || {
                        DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
                    },
                )?;
                if response_end != input.len() {
                    return Err(DecodeError::malformed(
                        response_end as u64,
                        MalformedKind::TrailingData,
                    ));
                }
                return Ok(JpipResponseSummary {
                    messages,
                    end_of_response_reason: Some(end.reason_code),
                });
            }
        }
        let next_position = position.checked_add(consumed).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                ensures result == crate::specs::part2_jpip_error(position, MalformedKind::ArithmeticOverflow),
            ))]
            || {
                DecodeError::malformed(position as u64, MalformedKind::ArithmeticOverflow)
            },
        )?;
        if next_position <= position || next_position > input.len() {
            return Err(DecodeError::malformed(
                position as u64,
                MalformedKind::InvalidJpipHeader,
            ));
        }
        position = next_position;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part2_jpip_response_remaining); }
    Ok(JpipResponseSummary {
        messages,
        end_of_response_reason: None,
    })
}
