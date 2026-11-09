//! Raw response parsing, actual fragment insertion and partial cache commits.

use super::*;

verus! {

pub type Part2JpipResponseSummary = (u64, Option<u8>);
pub type Part2JpipResponse = (Result<Part2JpipResponseSummary, crate::DecodeError>, Part2JpipCache);

#[verifier::opaque]
pub open spec fn part2_jpip_response_data(
    cache: Part2JpipCache, header: Part2JpipHeader, body: Seq<u8>, position: usize, messages: u64,
) -> (Result<u64, crate::DecodeError>, Part2JpipCache) {
    match part2_jpip_fragment_from_message(header, body, &cache.0) {
        Err(error) => (Err(error), cache),
        Ok(fragment) => {
            let inserted = part2_jpip_cache_insert(cache, fragment);
            match inserted.0 {
                Err(error) => (Err(error), inserted.1),
                Ok(()) => if messages == u64::MAX {
                    (Err(part2_jpip_error(position, crate::MalformedKind::ArithmeticOverflow)), inserted.1)
                } else { (Ok((messages + 1) as u64), inserted.1) },
            }
        },
    }
}

#[verifier::opaque]
pub open spec fn part2_jpip_response_remaining(
    input: Seq<u8>, cache: Part2JpipCache, context: Part2JpipContext,
    parser_limits: crate::ResourceLimits, position: usize, messages: u64,
) -> Part2JpipResponse
    decreases if (position as nat) < input.len() { input.len() - position as nat } else { 0 },
{
    if position as nat >= input.len() { (Ok((messages, None)), cache) }
    else {
        let parsed = part2_parse_jpip_message(input.subrange(position as int, input.len() as int), context, &parser_limits);
        match parsed.0 {
            Err(error) => (Err(error), cache),
            Ok((message, consumed)) => {
                if consumed == 0 { (Err(part2_jpip_error(position, crate::MalformedKind::InvalidJpipHeader)), cache) }
                else {
                    match message {
                        Part2JpipMessage::Data { header, body } => {
                            let data = part2_jpip_response_data(cache, header, body, position, messages);
                            match data.0 {
                                Err(error) => (Err(error), data.1),
                                Ok(next_messages) => {
                                    let next = position as nat + consumed as nat;
                                    if next > usize::MAX as nat {
                                        (Err(part2_jpip_error(position, crate::MalformedKind::ArithmeticOverflow)), data.1)
                                    } else if next <= position as nat || next > input.len() {
                                        (Err(part2_jpip_error(position, crate::MalformedKind::InvalidJpipHeader)), data.1)
                                    } else {
                                        part2_jpip_response_remaining(input, data.1, parsed.1, parser_limits, next as usize, next_messages)
                                    }
                                },
                            }
                        },
                        Part2JpipMessage::EndOfResponse { reason, .. } => {
                            let end = position as nat + consumed as nat;
                            if end > usize::MAX as nat {
                                (Err(part2_jpip_error(position, crate::MalformedKind::ArithmeticOverflow)), cache)
                            } else if end != input.len() {
                                (Err(part2_jpip_error(end as usize, crate::MalformedKind::TrailingData)), cache)
                            } else { (Ok((messages, Some(reason))), cache) }
                        },
                    }
                }
            },
        }
    }
}

pub open spec fn part2_ingest_jpip_response(input: Seq<u8>, cache: Part2JpipCache) -> Part2JpipResponse {
    part2_jpip_response_remaining(input, cache, (None, None), cache.0, 0, 0)
}

}
