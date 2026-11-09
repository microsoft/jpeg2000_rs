//! Required byte ranges, missing intervals, and progressive availability.

use super::{
    DatabinCache, DatabinId, DecodeError, JpipAvailability, JpipAvailabilityReport,
    JpipDatabinRange, JpipMissingRange, JpipPrecinctCodestreamPlan, JpipPrecinctPacket,
    MalformedKind, Resource,
};
#[cfg(verus_keep_ghost)]
use super::{
    databin_id_view, jpip_availability_outcome, jpip_availability_view, jpip_cache_fields,
    jpip_cache_view, jpip_databin_fields, jpip_databin_view, jpip_missing_view, jpip_missing_views,
    jpip_packet_bytes_outcome, jpip_packet_view, jpip_packets_view, jpip_range_outcome,
    jpip_range_view, jpip_ranges_view, jpip_status_view, jpip_stored_fragment_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl JpipDatabinRange {
    pub fn new(databin: DatabinId, offset: u64, length: u64) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                jpip_range_outcome(result),
                crate::specs::part2_jpip_range_new(databin_id_view(databin), offset, length),
            )
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_range_view); }
        if length == 0 {
            return Err(DecodeError::malformed(
                offset,
                MalformedKind::InvalidJpipFragment,
            ));
        }
        offset.checked_add(length).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(offset),
                ))]
            || DecodeError::malformed(offset, MalformedKind::ArithmeticOverflow),
        )?;
        Ok(Self {
            databin,
            offset,
            length,
        })
    }

    pub const fn databin(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: DatabinId| {
            vstd::prelude::equal(databin_id_view(result), jpip_range_view(*self).0)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_range_view); }
        self.databin
    }

    pub const fn offset(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(result, jpip_range_view(*self).1)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_range_view); }
        self.offset
    }

    pub const fn length(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: u64| {
            vstd::prelude::equal(result, jpip_range_view(*self).2)
        });
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_range_view); }
        self.length
    }
}

impl JpipMissingRange {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures databin_id_view(result) == jpip_missing_view(*self).0,))]
    pub const fn databin(&self) -> DatabinId {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_missing_view); }
        self.databin
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_missing_view(*self).1,))]
    pub const fn offset(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_missing_view); }
        self.offset
    }

    /// Returns `None` only when the data-bin has not announced its final
    /// length, so the required tail is not yet knowable.
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_missing_view(*self).2,))]
    pub const fn length(&self) -> Option<u64> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_missing_view); }
        self.length
    }
}

impl JpipAvailabilityReport {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_availability_view(self).0,))]
    pub const fn status(&self) -> JpipAvailability {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_availability_view); }
        self.status
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_availability_view(self).1,))]
    pub const fn required_bytes(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_availability_view); }
        self.required_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == jpip_availability_view(self).2,))]
    pub const fn available_bytes(&self) -> u64 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_availability_view); }
        self.available_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@.map_values(|range: JpipMissingRange| jpip_missing_view(range)) == jpip_availability_view(self).3,
    ))]
    pub fn missing_ranges(&self) -> &[JpipMissingRange] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_availability_view); }
        &self.missing
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == matches!(jpip_availability_view(self).0, JpipAvailability::Available),
    ))]
    pub const fn is_available(&self) -> bool {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_availability_view); }
        matches!(self.status, JpipAvailability::Available)
    }
}

impl DatabinCache {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_missing_views(&result) == crate::specs::part2_jpip_complete_missing(jpip_cache_view(self), databin_id_view(id)),
    ))]
    pub(super) fn complete_databin_missing(&self, id: DatabinId) -> Vec<JpipMissingRange> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(jpip_missing_view); }
        match self.status(id) {
            Some(status) => vec![JpipMissingRange {
                databin: id,
                offset: status.contiguous_prefix(),
                length: status.final_length().map(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: u64 =>
                        ensures result == crate::specs::part9_missing_length(length as nat,
                            if jpip_status_view(&status).1 < length { jpip_status_view(&status).1 as nat } else { length as nat }) as u64,
                    ))]
                    |length| {
                        crate::refinement::jpip_missing_length(
                            length,
                            status.contiguous_prefix().min(length),
                        )
                    },
                ),
            }],
            None => vec![JpipMissingRange {
                databin: id,
                offset: 0,
                length: None,
            }],
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_availability_outcome(result)
            == crate::specs::part2_jpip_cache_availability(jpip_cache_view(self), jpip_ranges_view(ranges)),
    ))]
    pub fn availability(
        &self,
        ranges: &[JpipDatabinRange],
    ) -> Result<JpipAvailabilityReport, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); reveal(jpip_range_view); reveal(jpip_missing_view); reveal(jpip_availability_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cache = jpip_cache_view(self);
            let ghost requests = jpip_ranges_view(ranges);
            let ghost expected = crate::specs::part2_jpip_cache_availability(cache, requests);
        }
        if ranges.len() as u64 > self.limits.maximum_packets() {
            return Err(DecodeError::limit(
                Resource::Packets,
                self.limits.maximum_packets(),
                ranges.len() as u64,
            ));
        }
        let mut required_bytes = 0_u64;
        let mut missing = Vec::new();
        let mut work = 0_u64;
        let mut range_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! { assert(jpip_missing_views(&missing) =~= Seq::<crate::specs::Part2JpipMissing>::empty()); }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant range_index <= ranges.len(),
                    cache == jpip_cache_view(self), cache.0 == self.limits,
                    cache.1.len() == self.databins.len(),
                    forall|index: int| 0 <= index < self.databins.len() ==>
                        #[trigger] cache.1[index] == jpip_databin_view(&self.databins@[index]),
                    requests == jpip_ranges_view(ranges), requests.len() == ranges.len(),
                    forall|index: int| 0 <= index < ranges.len() ==>
                        #[trigger] requests[index] == jpip_range_view(ranges@[index]),
                    expected == crate::specs::part2_jpip_cache_availability(cache, requests),
                    expected == crate::specs::part2_jpip_availability_remaining(cache, requests, range_index as nat,
                        required_bytes, work, jpip_missing_views(&missing)),
                decreases ranges.len() - range_index,
            )
        )]
        while range_index < ranges.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_availability_remaining);
                reveal(crate::specs::part2_jpip_availability_request);
            }
            let requested = ranges[range_index];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost request = jpip_range_view(requested);
                let ghost request_expected = crate::specs::part2_jpip_availability_request(
                    cache, request, required_bytes, work, jpip_missing_views(&missing));
            }
            let requested_end =
                requested
                    .offset
                    .checked_add(requested.length)
                    .ok_or_else(
                        #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(requested.offset),
                        ))]
                        || {
                            DecodeError::malformed(requested.offset, MalformedKind::ArithmeticOverflow)
                        },
                    )?;
            if requested_end > self.limits.maximum_input_bytes() {
                return Err(DecodeError::limit(
                    Resource::InputBytes,
                    self.limits.maximum_input_bytes(),
                    requested_end,
                ));
            }
            required_bytes = required_bytes.checked_add(requested.length).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(requested.offset),
                    ))]
                || DecodeError::malformed(requested.offset, MalformedKind::ArithmeticOverflow),
            )?;
            if required_bytes > self.limits.maximum_input_bytes() {
                return Err(DecodeError::limit(
                    Resource::InputBytes,
                    self.limits.maximum_input_bytes(),
                    required_bytes,
                ));
            }
            let Some(databin_index) = self.find_databin_index(requested.databin) else {
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost previous = jpip_missing_views(&missing); }
                missing.push(JpipMissingRange {
                    databin: requested.databin,
                    offset: requested.offset,
                    length: Some(requested.length),
                });
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(jpip_missing_views(&missing) =~= previous.push((request.0, request.1, Some(request.2))));
                }
                range_index += 1;
                continue;
            };
            let databin = self.databins.get(databin_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(requested.offset),
                ))]
                || DecodeError::malformed(requested.offset, MalformedKind::ArithmeticOverflow),
            )?;
            #[cfg(verus_keep_ghost)]
            proof! { jpip_databin_fields(databin); }
            let mut cursor = requested.offset;
            let mut fragment_index = 0_usize;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost fragments = cache.1[databin_index as int].1;
                let ghost scan_expected = crate::specs::part2_jpip_availability_fragments(
                    fragments, request, requested_end, 0, cursor, work,
                    jpip_missing_views(&missing), crate::limits::resource_work_limit(&cache.0));
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_availability_fragments); }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant fragment_index <= databin.fragments.len(),
                        databin_index < cache.1.len(),
                        fragments == cache.1[databin_index as int].1,
                        fragments.len() == databin.fragments.len(),
                        forall|index: int| 0 <= index < databin.fragments.len() ==>
                            #[trigger] fragments[index] == jpip_stored_fragment_view(&databin.fragments@[index]),
                        forall|index: int| 0 <= index < databin.fragments.len() ==>
                            #[trigger] fragments[index] == (databin.fragments@[index].offset, databin.fragments@[index].bytes@),
                        request == jpip_range_view(requested),
                        requested_end as nat == request.1 as nat + request.2 as nat,
                        requested.offset <= cursor <= requested_end,
                        cache.0 == self.limits,
                        cache == jpip_cache_view(self), requests == jpip_ranges_view(ranges),
                        expected == crate::specs::part2_jpip_cache_availability(cache, requests),
                        request_expected == match scan_expected {
                            Err(error) => Err(error),
                            Ok(scan) => Ok((required_bytes, scan.1,
                                if scan.0 < requested_end {
                                    scan.2.push((request.0, scan.0, Some((requested_end - scan.0) as u64)))
                                } else { scan.2 })),
                        },
                        expected == match request_expected {
                            Err(error) => Err(error),
                            Ok(next) => crate::specs::part2_jpip_availability_remaining(
                                cache, requests, range_index as nat + 1, next.0, next.1, next.2),
                        },
                        (fragment_index >= databin.fragments.len() || cursor >= requested_end) ==>
                            scan_expected == Ok((cursor, work, jpip_missing_views(&missing))),
                    invariant_except_break
                        scan_expected == crate::specs::part2_jpip_availability_fragments(
                            fragments, request, requested_end, fragment_index as nat, cursor, work,
                            jpip_missing_views(&missing), crate::limits::resource_work_limit(&cache.0)),
                    ensures scan_expected == Ok((cursor, work, jpip_missing_views(&missing))),
                    decreases databin.fragments.len() - fragment_index,
                )
            )]
            while fragment_index < databin.fragments.len() && cursor < requested_end {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_availability_fragments); }
                work = work.checked_add(1).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(cursor),
                    ))]
                    || DecodeError::malformed(cursor, MalformedKind::ArithmeticOverflow),
                )?;
                if work > self.limits.maximum_work_units() {
                    return Err(DecodeError::limit(
                        Resource::WorkUnits,
                        self.limits.maximum_work_units(),
                        work,
                    ));
                }
                let fragment = &databin.fragments[fragment_index];
                if fragment.end() <= cursor {
                    fragment_index += 1;
                    continue;
                }
                if fragment.offset >= requested_end {
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(scan_expected == Ok((cursor, work, jpip_missing_views(&missing)))); }
                    break;
                }
                if fragment.offset > cursor {
                    let missing_end = fragment.offset.min(requested_end);
                    #[cfg(verus_keep_ghost)]
                    proof_decl! { let ghost previous = jpip_missing_views(&missing); }
                    missing.push(JpipMissingRange {
                        databin: requested.databin,
                        offset: cursor,
                        length: Some(missing_end - cursor),
                    });
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(jpip_missing_views(&missing) =~= previous.push((request.0, cursor, Some((missing_end - cursor) as u64))));
                    }
                    cursor = missing_end;
                }
                if cursor < requested_end && fragment.end() > cursor {
                    cursor = fragment.end().min(requested_end);
                }
                fragment_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part2_jpip_availability_fragments);
                assert(scan_expected == Ok((cursor, work, jpip_missing_views(&missing))));
            }
            if cursor < requested_end {
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost previous = jpip_missing_views(&missing); }
                missing.push(JpipMissingRange {
                    databin: requested.databin,
                    offset: cursor,
                    length: Some(requested_end - cursor),
                });
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(jpip_missing_views(&missing) =~= previous.push((request.0, cursor, Some((requested_end - cursor) as u64))));
                }
            }
            range_index += 1;
        }
        let mut missing_bytes = 0_u64;
        let mut missing_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(crate::specs::part2_jpip_availability_remaining);
            reveal(crate::specs::part2_jpip_missing_total);
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost final_missing = jpip_missing_views(&missing);
            let ghost missing_total = crate::specs::part2_jpip_missing_total(final_missing, 0, 0);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant missing_index <= missing.len(),
                    final_missing == jpip_missing_views(&missing),
                    final_missing.len() == missing.len(),
                    forall|index: int| 0 <= index < missing.len() ==>
                        #[trigger] final_missing[index] == jpip_missing_view(missing@[index]),
                    expected == crate::specs::part2_jpip_availability_finish(required_bytes, final_missing),
                    cache == jpip_cache_view(self), requests == jpip_ranges_view(ranges),
                    expected == crate::specs::part2_jpip_cache_availability(cache, requests),
                    missing_total == crate::specs::part2_jpip_missing_total(final_missing, missing_index as nat, missing_bytes),
                    missing_total == crate::specs::part2_jpip_missing_total(final_missing, 0, 0),
                decreases missing.len() - missing_index,
            )
        )]
        while missing_index < missing.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_missing_total); }
            missing_bytes = missing_bytes
                .checked_add(missing[missing_index].length.unwrap_or(0))
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                    ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
            missing_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_missing_total); }
        let available_bytes = required_bytes.checked_sub(missing_bytes).ok_or_else(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(0),
                ))]
            || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?;
        if missing_bytes > required_bytes
            || crate::refinement::jpip_available_bytes(required_bytes, missing_bytes)
                != available_bytes
        {
            return Err(DecodeError::malformed(0, MalformedKind::ArithmeticOverflow));
        }
        Ok(JpipAvailabilityReport {
            status: if crate::refinement::jpip_range_complete(available_bytes, required_bytes) {
                JpipAvailability::Available
            } else if available_bytes == 0 {
                JpipAvailability::Missing
            } else {
                JpipAvailability::Partial
            },
            required_bytes,
            available_bytes,
            missing,
        })
    }

    pub(super) fn precinct_availability(
        &self,
        plan: &JpipPrecinctCodestreamPlan,
        packet_end: usize,
    ) -> Result<JpipAvailabilityReport, DecodeError> {
        let packets = plan
            .packets
            .get(..packet_end)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let ranges: Vec<JpipDatabinRange> = packets.iter().map(|packet| packet.range).collect();
        let mut report = self.availability(&ranges)?;
        self.append_complete_databin_requirement(plan.main_header, &mut report)?;
        self.append_complete_databin_requirement(plan.tile_header, &mut report)?;
        report.status = if report.missing.is_empty() {
            JpipAvailability::Available
        } else if report.available_bytes == 0 {
            JpipAvailability::Missing
        } else {
            JpipAvailability::Partial
        };
        Ok(report)
    }

    fn append_complete_databin_requirement(
        &self,
        id: DatabinId,
        report: &mut JpipAvailabilityReport,
    ) -> Result<(), DecodeError> {
        let Some(status) = self.status(id) else {
            report.missing.push(JpipMissingRange {
                databin: id,
                offset: 0,
                length: None,
            });
            return Ok(());
        };
        let Some(final_length) = status.final_length() else {
            report.available_bytes = report
                .available_bytes
                .checked_add(status.contiguous_prefix())
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            report.missing.push(JpipMissingRange {
                databin: id,
                offset: status.contiguous_prefix(),
                length: None,
            });
            return Ok(());
        };
        let header_report = if final_length == 0 {
            JpipAvailabilityReport {
                status: JpipAvailability::Available,
                required_bytes: 0,
                available_bytes: 0,
                missing: Vec::new(),
            }
        } else {
            self.availability(&[JpipDatabinRange::new(id, 0, final_length)?])?
        };
        report.required_bytes = report
            .required_bytes
            .checked_add(header_report.required_bytes)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        report.available_bytes = report
            .available_bytes
            .checked_add(header_report.available_bytes)
            .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
        let mut missing_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant missing_index <= header_report.missing.len(),
                decreases header_report.missing.len() - missing_index,
            )
        )]
        while missing_index < header_report.missing.len() {
            report.missing.push(header_report.missing[missing_index]);
            missing_index += 1;
        }
        Ok(())
    }

    pub(super) fn progressive_availability(
        &self,
        plan: &JpipPrecinctCodestreamPlan,
    ) -> Result<(u16, Vec<JpipMissingRange>), DecodeError> {
        let mut header_report = JpipAvailabilityReport {
            status: JpipAvailability::Available,
            required_bytes: 0,
            available_bytes: 0,
            missing: Vec::new(),
        };
        self.append_complete_databin_requirement(plan.main_header, &mut header_report)?;
        self.append_complete_databin_requirement(plan.tile_header, &mut header_report)?;
        if !header_report.missing.is_empty() {
            return Ok((0, header_report.missing));
        }
        let mut layer = 0_usize;
        let mut start = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant start <= plan.packets.len(),
                decreases plan.layer_ends.len() - layer,
            )
        )]
        while layer < plan.layer_ends.len() {
            let end = *plan
                .layer_ends
                .get(layer)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            let packet_layer = plan
                .packets
                .get(start..end)
                .ok_or_else(|| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?;
            let ranges: Vec<JpipDatabinRange> =
                packet_layer.iter().map(|packet| packet.range).collect();
            let report = self.availability(&ranges)?;
            if !report.is_available() {
                return Ok((
                    u16::try_from(layer).map_err(|_| {
                        DecodeError::malformed(0, MalformedKind::ArithmeticOverflow)
                    })?,
                    report.missing,
                ));
            }
            start = end;
            layer += 1;
        }
        Ok((
            u16::try_from(layer)
                .map_err(|_| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow))?,
            Vec::new(),
        ))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures jpip_packet_bytes_outcome(result)
            == crate::specs::part2_jpip_read_packets(jpip_cache_view(self), jpip_packets_view(packets)),
    ))]
    pub(super) fn read_packet_ranges(
        &self,
        packets: &[JpipPrecinctPacket],
    ) -> Result<Vec<u8>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { jpip_cache_fields(self); reveal(jpip_packet_view); reveal(jpip_range_view); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost cache = jpip_cache_view(self);
            let ghost entries = jpip_packets_view(packets);
            let ghost expected = crate::specs::part2_jpip_read_packets(cache, entries);
            let ghost total_expected = crate::specs::part2_jpip_packet_total(entries, 0, 0);
        }
        let mut total = 0_u64;
        let mut packet_index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant packet_index <= packets.len(),
                    cache == jpip_cache_view(self),
                    entries == jpip_packets_view(packets), entries.len() == packets.len(),
                    forall|index: int| 0 <= index < packets.len() ==>
                        #[trigger] entries[index] == (jpip_range_view(packets@[index].range), packets@[index].layer),
                    total_expected == crate::specs::part2_jpip_packet_total(entries, 0, 0),
                    total_expected == crate::specs::part2_jpip_packet_total(entries, packet_index as nat, total),
                    expected == crate::specs::part2_jpip_read_packets(cache, entries),
                decreases packets.len() - packet_index,
            )
        )]
        while packet_index < packets.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_packet_total); }
            total = total
                .checked_add(packets[packet_index].range.length)
                .ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                    ))]
                    || DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
                )?;
            packet_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_packet_total); }
        if total > self.limits.maximum_input_bytes() {
            return Err(DecodeError::limit(
                Resource::InputBytes,
                self.limits.maximum_input_bytes(),
                total,
            ));
        }
        let mut output = Vec::with_capacity(usize::try_from(total).map_err(
            #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(0),
                    ))]
            |_error| DecodeError::malformed(0, MalformedKind::ArithmeticOverflow),
        )?);
        packet_index = 0;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant packet_index <= packets.len(),
                    cache == jpip_cache_view(self), cache.0 == self.limits,
                    cache.1.len() == self.databins.len(),
                    forall|index: int| 0 <= index < self.databins.len() ==>
                        #[trigger] cache.1[index] == jpip_databin_view(&self.databins@[index]),
                    entries == jpip_packets_view(packets), entries.len() == packets.len(),
                    forall|index: int| 0 <= index < packets.len() ==>
                        #[trigger] entries[index] == (jpip_range_view(packets@[index].range), packets@[index].layer),
                    expected == crate::specs::part2_jpip_read_packets(cache, entries),
                    expected == crate::specs::part2_jpip_packet_remaining(cache, entries, packet_index as nat, output@),
                decreases packets.len() - packet_index,
            )
        )]
        while packet_index < packets.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_packet_remaining); }
            let range = packets[packet_index].range;
            let databin_index = self.find_databin_index(range.databin).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_cache_error(range.offset, MalformedKind::MissingRequiredStructure),
                ))]
                || {
                    DecodeError::malformed(range.offset, MalformedKind::MissingRequiredStructure)
                },
            )?;
            let databin = self.databins.get(databin_index).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(range.offset),
                ))]
                || DecodeError::malformed(range.offset, MalformedKind::ArithmeticOverflow),
            )?;
            let end = range.offset.checked_add(range.length).ok_or_else(
                #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                    ensures result == crate::specs::part2_jpip_range_overflow(range.offset),
                ))]
                || DecodeError::malformed(range.offset, MalformedKind::ArithmeticOverflow),
            )?;
            #[cfg(verus_keep_ghost)]
            proof! { jpip_databin_fields(databin); }
            let mut cursor = range.offset;
            let mut fragment_index = 0_usize;
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost fragments = cache.1[databin_index as int].1;
                let ghost scan_expected = crate::specs::part2_jpip_packet_fragments(fragments, 0, cursor, end, output@);
            }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant fragment_index <= databin.fragments.len(),
                        fragments == cache.1[databin_index as int].1,
                        databin_index < cache.1.len(), fragments.len() == databin.fragments.len(),
                        forall|index: int| 0 <= index < databin.fragments.len() ==>
                            #[trigger] fragments[index] == jpip_stored_fragment_view(&databin.fragments@[index]),
                        forall|index: int| 0 <= index < databin.fragments.len() ==>
                            #[trigger] fragments[index] == (databin.fragments@[index].offset, databin.fragments@[index].bytes@),
                        range.offset <= cursor <= end,
                        cache == jpip_cache_view(self), entries == jpip_packets_view(packets),
                        expected == crate::specs::part2_jpip_read_packets(cache, entries),
                        expected == match scan_expected {
                            Err(error) => Err(error),
                            Ok(bytes) => crate::specs::part2_jpip_packet_remaining(cache, entries, packet_index as nat + 1, bytes),
                        },
                        scan_expected == crate::specs::part2_jpip_packet_fragments(
                            fragments, fragment_index as nat, cursor, end, output@),
                    decreases databin.fragments.len() - fragment_index,
                )
            )]
            while fragment_index < databin.fragments.len() && cursor < end {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part2_jpip_packet_fragments); }
                let fragment = &databin.fragments[fragment_index];
                if fragment.end() <= cursor {
                    fragment_index += 1;
                    continue;
                }
                if fragment.offset > cursor {
                    return Err(DecodeError::malformed(
                        cursor,
                        MalformedKind::MissingRequiredStructure,
                    ));
                }
                let copy_end = fragment.end().min(end);
                let local_start = usize::try_from(cursor - fragment.offset).map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(cursor),
                    ))]
                    |_error| DecodeError::malformed(cursor, MalformedKind::ArithmeticOverflow),
                )?;
                let local_end = usize::try_from(copy_end.checked_sub(fragment.offset).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(cursor),
                        ))]
                    || DecodeError::malformed(cursor, MalformedKind::ArithmeticOverflow),
                )?)
                .map_err(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                            ensures result == crate::specs::part2_jpip_range_overflow(cursor),
                        ))]
                    |_error| DecodeError::malformed(cursor, MalformedKind::ArithmeticOverflow),
                )?;
                #[cfg(verus_keep_ghost)]
                proof_decl! { let ghost previous_output = output@; }
                output.extend_from_slice(fragment.bytes.get(local_start..local_end).ok_or_else(
                    #[cfg_attr(verus_keep_ghost, verus_spec(result: DecodeError =>
                        ensures result == crate::specs::part2_jpip_range_overflow(cursor),
                    ))]
                    || DecodeError::malformed(cursor, MalformedKind::ArithmeticOverflow),
                )?);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(local_start as nat == cursor as nat - fragment.offset as nat);
                    assert(local_end as nat == copy_end as nat - fragment.offset as nat);
                    assert(output@ =~= previous_output + fragment.bytes@.subrange(local_start as int, local_end as int));
                    assert(scan_expected == crate::specs::part2_jpip_packet_fragments(
                        fragments, fragment_index as nat + 1, copy_end, end, output@));
                }
                cursor = copy_end;
                fragment_index += 1;
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part2_jpip_packet_fragments); }
            if cursor != end {
                return Err(DecodeError::malformed(
                    cursor,
                    MalformedKind::MissingRequiredStructure,
                ));
            }
            packet_index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part2_jpip_packet_remaining); }
        Ok(output)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures jpip_missing_views(final(output)) == jpip_missing_views(old(output))
        + input@.map_values(|range: JpipMissingRange| jpip_missing_view(range)),
))]
pub(super) fn append_missing_ranges(
    output: &mut Vec<JpipMissingRange>,
    input: &[JpipMissingRange],
) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = jpip_missing_views(output);
        let ghost incoming = input@.map_values(|range: JpipMissingRange| jpip_missing_view(range));
    }
    let mut index = 0_usize;
    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(
            invariant index <= input.len(),
                original == jpip_missing_views(old(output)),
                incoming == input@.map_values(|range: JpipMissingRange| jpip_missing_view(range)),
                jpip_missing_views(output) == original + incoming.subrange(0, index as int),
            decreases input.len() - index,
        )
    )]
    while index < input.len() {
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = jpip_missing_views(output); }
        output.push(input[index]);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(jpip_missing_views(output) =~= previous.push(incoming[index as int]));
            assert(incoming.subrange(0, index as int + 1) =~= incoming.subrange(0, index as int).push(incoming[index as int]));
        }
        index += 1;
    }
}
