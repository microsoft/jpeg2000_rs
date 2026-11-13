//! Structural admission only; the strict decoder must still validate all data.

use super::reader::new_parser;
use super::{COD, DecodeError, MalformedKind, Parser, QCD, ResourceLimits};
#[cfg(verus_keep_ghost)]
use super::{
    layout_prologue_outcome, main_header_segment_outcome, parsed_image_size_view,
    parser_initial_outcome, parser_view, tile_part_header_outcome, tile_part_header_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
pub(crate) struct RecoveryFraming {
    pub(crate) append_eoc: bool,
    pub(crate) work_units: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn framing_outcome(result: Result<RecoveryFraming, DecodeError>)
        -> Result<(bool, u64), DecodeError>
    {
        match result {
            Ok(frame) => Ok((frame.append_eoc, frame.work_units)),
            Err(error) => Err(error),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures framing_outcome(result) == crate::specs::raw_recovery_framing(input@, limits),
))]
pub(crate) fn recovery_framing(
    input: &[u8],
    limits: &ResourceLimits,
) -> Result<RecoveryFraming, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(crate::specs::raw_recovery_framing);
        reveal(parser_initial_outcome);
        reveal(layout_prologue_outcome);
        reveal(parsed_image_size_view);
        reveal(super::selection_geometry_view);
        reveal(parser_view);
    }
    let mut parser = new_parser(input, limits)?;
    let (size, _, _) = parser.parse_layout_prologue()?;
    if size.tiles_across != 1 || size.tiles_down != 1 {
        return Ok(RecoveryFraming {
            append_eoc: false,
            work_units: parser.work_units,
        });
    }
    parser.recovery_main_headers()
}

impl<'a> Parser<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (framing_outcome(result), parser_view(final(self)))
            == crate::specs::raw_recovery_main_headers(parser_view(old(self)), 1, false, false),
    ))]
    fn recovery_main_headers(&mut self) -> Result<RecoveryFraming, DecodeError> {
        let mut count = 1u64;
        let mut cod = false;
        let mut qcd = false;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = parser_view(self);
            let ghost goal = crate::specs::raw_recovery_main_headers(initial, 1, false, false);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::raw_recovery_main_headers); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant initial == parser_view(old(self)),
                goal == crate::specs::raw_recovery_main_headers(initial, 1, false, false),
                goal == crate::specs::raw_recovery_main_loop(parser_view(self), count, cod, qcd, initial.input.len()),
                self.input@ == initial.input,
            decreases self.input.len() as int - self.position as int,
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::raw_recovery_main_loop, 1);
                reveal(main_header_segment_outcome);
                reveal(parser_view);
                reveal(crate::specs::part1_read_main_header_segment);
                reveal(crate::specs::part1_codestream_read_segment);
                reveal(crate::specs::part1_codestream_charge_work);
            }
            let before = self.position;
            match self.read_main_header_segment(&mut count)? {
                Some(segment) => {
                    cod |= segment.marker == COD;
                    qcd |= segment.marker == QCD;
                    if self.position <= before || self.position > self.input.len() {
                        return Err(self.malformed_here(MalformedKind::InvalidMarkerLength));
                    }
                }
                None => {
                    if !cod || !qcd {
                        return Err(self.malformed_here(MalformedKind::MissingRequiredStructure));
                    }
                    return self.recovery_sot();
                }
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (framing_outcome(result), parser_view(final(self)))
            == crate::specs::raw_recovery_sot(parser_view(old(self))),
    ))]
    fn recovery_sot(&mut self) -> Result<RecoveryFraming, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::raw_recovery_sot);
            reveal(tile_part_header_outcome);
            reveal(tile_part_header_view);
            reveal(parser_view);
        }
        let part = self.read_sot(1)?;
        if part.length != 0 || part.tile_part_index != 0 || part.tile_part_count > 1 {
            return Ok(RecoveryFraming {
                append_eoc: false,
                work_units: self.work_units,
            });
        }
        self.recovery_tile_headers()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (framing_outcome(result), parser_view(final(self)))
            == crate::specs::raw_recovery_tile_headers(parser_view(old(self))),
    ))]
    fn recovery_tile_headers(&mut self) -> Result<RecoveryFraming, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = parser_view(self);
            let ghost goal = crate::specs::raw_recovery_tile_headers(initial);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::raw_recovery_tile_headers); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant initial == parser_view(old(self)),
                goal == crate::specs::raw_recovery_tile_headers(initial),
                goal == crate::specs::raw_recovery_tile_loop(parser_view(self), initial.input.len()),
                self.input@ == initial.input,
            decreases self.input.len() as int - self.position as int,
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::raw_recovery_tile_loop, 1);
                reveal(main_header_segment_outcome);
                reveal(parser_view);
                reveal(crate::specs::part1_read_tile_header_segment);
                reveal(crate::specs::part1_codestream_read_segment);
                reveal(crate::specs::part1_codestream_expect_standalone);
                reveal(crate::specs::part1_codestream_charge_work);
            }
            let before = self.position;
            match self.read_tile_header_segment()? {
                None => return self.recovery_body(),
                Some(_) => {
                    if self.position <= before || self.position > self.input.len() {
                        return Err(self.malformed_here(MalformedKind::InvalidMarkerLength));
                    }
                }
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (framing_outcome(result), parser_view(final(self)))
            == crate::specs::raw_recovery_body(parser_view(old(self))),
    ))]
    fn recovery_body(&mut self) -> Result<RecoveryFraming, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial = parser_view(self);
            let ghost goal = crate::specs::raw_recovery_body(initial);
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::raw_recovery_body); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant initial == parser_view(old(self)),
                goal == crate::specs::raw_recovery_body(initial),
                goal == crate::specs::raw_recovery_body_loop(parser_view(self), initial.input.len()),
                self.input@ == initial.input,
            decreases self.input.len() as int - self.position as int,
        ))]
        loop {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal_with_fuel(crate::specs::raw_recovery_body_loop, 1);
                reveal(parser_view);
            }
            if self.position >= self.input.len() {
                return Ok(RecoveryFraming {
                    append_eoc: true,
                    work_units: self.work_units,
                });
            }
            let start = self.position;
            let remaining = self.input.len() - start;
            let mut step = 1usize;
            if self.input[start] == 0xff && remaining >= 2 {
                let next = self.input[start + 1];
                if next <= 0x8f || next == 0x92 {
                    step = 2;
                } else if next == 0x91 {
                    if remaining < 6 {
                        return Err(self.malformed_here(MalformedKind::Truncated));
                    }
                    if self.input[start + 2] != 0 || self.input[start + 3] != 4 {
                        return Err(self.malformed_here(MalformedKind::InvalidMarkerLength));
                    }
                    step = 6;
                } else if next != 0xff {
                    // This includes EOC (with or without a trailer) and another
                    // SOT. Never append, discard a suffix, or retry a decode.
                    return Ok(RecoveryFraming {
                        append_eoc: false,
                        work_units: self.work_units,
                    });
                }
            }
            self.charge_work(step as u64)?;
            self.position = start + step;
        }
    }
}
