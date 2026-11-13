use super::errors::{packet_arithmetic_overflow, packet_reader_error, packet_reader_limit};
use super::{
    DecodeError, MalformedKind, PacketCoordinate, PacketGrid, PacketGridCountState, PacketIterator,
    ProgressionChange, ProgressionChanges, ProgressionOrder, ProgressionPacketIterator, Resource,
    ResourceLimits,
};
#[cfg(verus_keep_ghost)]
use super::{
    packet_grid_count_outcome, packet_grid_count_view, packet_grid_outcome, packet_grid_view,
    packet_iterator_view, packet_selection_view, packet_unravel_outcome,
    progression_packet_iterator_outcome, progression_packet_iterator_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_grid_resolution_summary(values@, 0, 0, false),
))]
fn packet_grid_resolution_summary(values: &[u8]) -> Result<(u8, bool), DecodeError> {
    let mut maximum = 0_u8;
    let mut zero = false;
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_grid_resolution_summary); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= values@.len(),
            crate::specs::part1_grid_resolution_summary(values@, 0, 0, false)
                == crate::specs::part1_grid_resolution_summary(values@, index, maximum, zero),
        decreases values@.len() - index,
    ))]
    while index < values.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_grid_resolution_summary); }
        let resolution = match values.get(index) {
            Some(resolution) => *resolution,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        if resolution == 0 {
            zero = true;
        }
        maximum = maximum.max(resolution);
        index = match index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_grid_resolution_summary); }
    Ok((maximum, zero))
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_grid_count_outcome(result) == crate::specs::part1_grid_count_summary(
        counts@,component_resolutions@,resolutions,expected),
))]
fn packet_grid_count_summary(
    counts: &[u32],
    component_resolutions: &[u8],
    resolutions: u8,
    expected: usize,
) -> Result<PacketGridCountState, DecodeError> {
    let capacity = match expected.checked_add(1) {
        Some(capacity) => capacity,
        None => return Err(packet_arithmetic_overflow()),
    };
    let mut state = PacketGridCountState {
        index: 0,
        component: 0,
        resolution: 0,
        total: 0,
        maximum: 0,
        offsets: Vec::with_capacity(capacity),
    };
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_grid_count_summary_run); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant state.index <= counts@.len(),
            crate::specs::part1_grid_count_summary(counts@,component_resolutions@,resolutions,expected)
            == crate::specs::part1_grid_count_summary_run(counts@,component_resolutions@,resolutions,packet_grid_count_view(&state)),
        decreases counts@.len()-state.index,
    ))]
    while state.index < counts.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_grid_count_summary_run); }
        let offset = match usize::try_from(state.total) {
            Ok(offset) => offset,
            Err(_) => return Err(packet_arithmetic_overflow()),
        };
        state.offsets.push(offset);
        let precincts = counts[state.index];
        let available = match component_resolutions.get(state.component) {
            Some(count) => usize::from(*count),
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        if state.resolution >= available && precincts != 0 {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        state.total = match state.total.checked_add(u64::from(precincts)) {
            Some(total) => total,
            None => return Err(packet_arithmetic_overflow()),
        };
        if precincts > state.maximum {
            state.maximum = precincts;
        }
        state.index = match state.index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        state.resolution = match state.resolution.checked_add(1) {
            Some(resolution) => resolution,
            None => return Err(packet_arithmetic_overflow()),
        };
        if state.resolution == usize::from(resolutions) {
            state.resolution = 0;
            state.component = match state.component.checked_add(1) {
                Some(component) => component,
                None => return Err(packet_arithmetic_overflow()),
            };
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_grid_count_summary_run); }
    let offset = match usize::try_from(state.total) {
        Ok(offset) => offset,
        Err(_) => return Err(packet_arithmetic_overflow()),
    };
    state.offsets.push(offset);
    Ok(state)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_grid_selected_precincts(
        packet_selection_view(selection),component_resolutions@,counts@,resolutions,components,initial_total),
))]
fn packet_grid_selected_precincts(
    selection: Option<&[u8]>,
    component_resolutions: &[u8],
    counts: &[u32],
    resolutions: u8,
    components: u16,
    initial_total: u64,
) -> Result<u64, DecodeError> {
    let Some(selected) = selection else {
        return Ok(initial_total);
    };
    if selected.len() != usize::from(components) {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    let mut total = 0_u64;
    let mut component = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_grid_selected_components);}
    #[cfg_attr(verus_keep_ghost,verus_spec(
        invariant component<=selected@.len(),
            packet_selection_view(selection)==Some(selected@),
            selected@.len()==components as nat,
            crate::specs::part1_grid_selected_precincts(packet_selection_view(selection),component_resolutions@,counts@,resolutions,components,initial_total)
                ==crate::specs::part1_grid_selected_components(selected@,component_resolutions@,counts@,resolutions,component,total),
        decreases selected@.len()-component,
    ))]
    while component < selected.len() {
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_grid_selected_components);}
        let count = match selected.get(component) {
            Some(count) => *count,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        let available = match component_resolutions.get(component) {
            Some(count) => *count,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        if count == 0 || count > available {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        let mut resolution = 0_u8;
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_grid_selected_row);}
        #[cfg_attr(verus_keep_ghost,verus_spec(
            invariant resolution<=count,
                packet_selection_view(selection)==Some(selected@),
                selected@.len()==components as nat,
                crate::specs::part1_grid_selected_precincts(packet_selection_view(selection),component_resolutions@,counts@,resolutions,components,initial_total)
                    ==match crate::specs::part1_grid_selected_row(counts@,resolutions,component,resolution,count,total) {
                        Err(error)=>Err(error),
                        Ok(total)=>crate::specs::part1_grid_selected_components(
                            selected@,component_resolutions@,counts@,resolutions,(component+1) as usize,total),
                    },
            decreases count-resolution,
        ))]
        while resolution < count {
            #[cfg(verus_keep_ghost)]
            proof! {reveal(crate::specs::part1_grid_selected_row);}
            let product = match component.checked_mul(usize::from(resolutions)) {
                Some(product) => product,
                None => return Err(packet_arithmetic_overflow()),
            };
            let index = match product.checked_add(usize::from(resolution)) {
                Some(index) => index,
                None => return Err(packet_arithmetic_overflow()),
            };
            let amount = match counts.get(index) {
                Some(amount) => u64::from(*amount),
                None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
            };
            total = match total.checked_add(amount) {
                Some(total) => total,
                None => return Err(packet_arithmetic_overflow()),
            };
            resolution = match resolution.checked_add(1) {
                Some(value) => value,
                None => return Err(packet_arithmetic_overflow()),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {reveal(crate::specs::part1_grid_selected_row);}
        component = match component.checked_add(1) {
            Some(value) => value,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! {reveal(crate::specs::part1_grid_selected_components);}
    Ok(total)
}

impl PacketGrid {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_packet_grid_total_precincts(packet_grid_view(self)),
    ))]
    pub fn total_precinct_count(&self) -> Result<u64, DecodeError> {
        match self.packet_count.checked_div(u64::from(self.layers)) {
            Some(count) => Ok(count),
            None => Err(packet_arithmetic_overflow()),
        }
    }

    pub fn new(
        layers: u16,
        components: u16,
        resolutions: u8,
        precinct_counts: Vec<u32>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        Self::new_with_component_resolutions(
            layers,
            components,
            vec![resolutions; usize::from(components)],
            precinct_counts,
            limits,
        )
    }

    pub(crate) fn new_with_component_resolutions(
        layers: u16,
        components: u16,
        component_resolutions: Vec<u8>,
        precinct_counts: Vec<u32>,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        packet_grid_new_with_component_resolutions(
            layers,
            components,
            component_resolutions,
            precinct_counts,
            limits,
        )
    }
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures packet_grid_outcome(result)==crate::specs::part1_packet_grid_new(
        layers,components,component_resolutions@,precinct_counts@,None,limits),
))]
pub(crate) fn packet_grid_new_with_component_resolutions(
    layers: u16,
    components: u16,
    component_resolutions: Vec<u8>,
    precinct_counts: Vec<u32>,
    limits: &ResourceLimits,
) -> Result<PacketGrid, DecodeError> {
    packet_grid_new_with_selected_resolutions(
        layers,
        components,
        component_resolutions,
        precinct_counts,
        None,
        limits,
    )
}

#[cfg_attr(verus_keep_ghost,verus_spec(result =>
    ensures packet_grid_outcome(result)==crate::specs::part1_packet_grid_new(
        layers,components,component_resolutions@,precinct_counts@,packet_selection_view(selected_resolution_counts),limits),
))]
pub(crate) fn packet_grid_new_with_selected_resolutions(
    layers: u16,
    components: u16,
    component_resolutions: Vec<u8>,
    precinct_counts: Vec<u32>,
    selected_resolution_counts: Option<&[u8]>,
    limits: &ResourceLimits,
) -> Result<PacketGrid, DecodeError> {
    let (resolutions, has_zero_resolution) =
        packet_grid_resolution_summary(&component_resolutions)?;
    if layers == 0 || components == 0 {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    if resolutions == 0 {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    if component_resolutions.len() != usize::from(components) || has_zero_resolution {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    if layers > limits.maximum_layers() {
        return Err(packet_reader_limit(
            Resource::Layers,
            u64::from(limits.maximum_layers()),
            u64::from(layers),
        ));
    }
    if components > limits.maximum_components() {
        return Err(packet_reader_limit(
            Resource::Components,
            u64::from(limits.maximum_components()),
            u64::from(components),
        ));
    }
    if resolutions > limits.maximum_resolutions_per_component() {
        return Err(packet_reader_limit(
            Resource::Resolutions,
            u64::from(limits.maximum_resolutions_per_component()),
            u64::from(resolutions),
        ));
    }
    let expected_counts = match usize::from(components).checked_mul(usize::from(resolutions)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    if precinct_counts.len() != expected_counts {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }

    let summary = packet_grid_count_summary(
        &precinct_counts,
        &component_resolutions,
        resolutions,
        expected_counts,
    )?;
    let total_precincts = summary.total;
    let maximum_precincts_per_resolution = summary.maximum;
    let precinct_offsets = summary.offsets;
    let selected_precincts = packet_grid_selected_precincts(
        selected_resolution_counts,
        &component_resolutions,
        &precinct_counts,
        resolutions,
        components,
        total_precincts,
    )?;
    if selected_precincts > limits.maximum_precincts() {
        return Err(packet_reader_limit(
            Resource::Precincts,
            limits.maximum_precincts(),
            selected_precincts,
        ));
    }
    let packet_count = match total_precincts.checked_mul(u64::from(layers)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    let selected_packet_count = match selected_precincts.checked_mul(u64::from(layers)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    if selected_packet_count > limits.maximum_packets() {
        return Err(packet_reader_limit(
            Resource::Packets,
            limits.maximum_packets(),
            selected_packet_count,
        ));
    }
    let first = match u64::from(layers).checked_mul(u64::from(components)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    let second = match first.checked_mul(u64::from(resolutions)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    let candidate_count = match second.checked_mul(u64::from(maximum_precincts_per_resolution)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    if candidate_count > limits.maximum_work_units() {
        return Err(packet_reader_limit(
            Resource::WorkUnits,
            limits.maximum_work_units(),
            candidate_count,
        ));
    }
    Ok(PacketGrid {
        layers,
        components,
        resolutions,
        component_resolutions,
        maximum_precincts_per_resolution,
        precinct_counts,
        precinct_offsets,
        candidate_count,
        packet_count,
    })
}

impl PacketGrid {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == packet_grid_view(self).packet_count,))]
    pub const fn packet_count(&self) -> u64 {
        self.packet_count
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_packet_grid_selected_count(packet_grid_view(self), resolution_counts@),
    ))]
    pub(crate) fn selected_packet_count(
        &self,
        resolution_counts: &[u8],
    ) -> Result<u64, DecodeError> {
        if resolution_counts.len() != usize::from(self.components) {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_selected_count_run); }
        let mut precincts = 0_u64;
        let mut component = 0_u16;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant component <= self.components,
                    crate::specs::part1_packet_grid_selected_count(packet_grid_view(self), resolution_counts@)
                        == crate::specs::part1_packet_selected_count_run(packet_grid_view(self), resolution_counts@, component, precincts),
                decreases self.components - component,
            )
        )]
        while component < self.components {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_packet_selected_count_run); }
            let count = match resolution_counts.get(usize::from(component)) {
                Some(count) => *count,
                None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
            };
            if count == 0 {
                return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
            }
            let available = match self.component_resolutions.get(usize::from(component)) {
                Some(count) => *count,
                None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
            };
            if count > available {
                return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_packet_selected_row); }
            let mut resolution = 0_u8;
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant resolution <= count,
                        crate::specs::part1_packet_grid_selected_count(packet_grid_view(self), resolution_counts@)
                            == match crate::specs::part1_packet_selected_row(packet_grid_view(self), component, resolution, count, precincts) {
                                Err(error) => Err(error),
                                Ok(total) => crate::specs::part1_packet_selected_count_run(
                                    packet_grid_view(self), resolution_counts@, (component + 1) as u16, total),
                            },
                    decreases count - resolution,
                )
            )]
            while resolution < count {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::specs::part1_packet_selected_count_run);
                    reveal(crate::specs::part1_packet_selected_row);
                }
                let amount = u64::from(self.precinct_count(component, resolution)?);
                precincts = match precincts.checked_add(amount) {
                    Some(total) => total,
                    None => return Err(packet_arithmetic_overflow()),
                };
                resolution = match resolution.checked_add(1) {
                    Some(resolution) => resolution,
                    None => return Err(packet_arithmetic_overflow()),
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_packet_selected_row); }
            component = match component.checked_add(1) {
                Some(component) => component,
                None => return Err(packet_arithmetic_overflow()),
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_selected_count_run); }
        match precincts.checked_mul(u64::from(self.layers)) {
            Some(total) => Ok(total),
            None => Err(packet_arithmetic_overflow()),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_packet_grid_precinct_count(packet_grid_view(self), component, resolution),
    ))]
    pub fn precinct_count(&self, component: u16, resolution: u8) -> Result<u32, DecodeError> {
        if component >= self.components || resolution >= self.resolutions {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        let component_resolution_count =
            match self.component_resolutions.get(usize::from(component)) {
                Some(count) => *count,
                None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
            };
        if resolution >= component_resolution_count {
            return Ok(0);
        }
        let product = match usize::from(component).checked_mul(usize::from(self.resolutions)) {
            Some(product) => product,
            None => return Err(packet_arithmetic_overflow()),
        };
        let index = match product.checked_add(usize::from(resolution)) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        if index >= self.precinct_counts.len() {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }
        Ok(self.precinct_counts[index])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_packet_grid_precinct_index(packet_grid_view(self), component, resolution, precinct),
    ))]
    pub fn precinct_index(
        &self,
        component: u16,
        resolution: u8,
        precinct: u32,
    ) -> Result<usize, DecodeError> {
        let count = self.precinct_count(component, resolution)?;
        if precinct >= count {
            return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
        }

        let product = match usize::from(component).checked_mul(usize::from(self.resolutions)) {
            Some(product) => product,
            None => return Err(packet_arithmetic_overflow()),
        };
        let component_resolution = match product.checked_add(usize::from(resolution)) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        let start = match self.precinct_offsets.get(component_resolution) {
            Some(start) => *start,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle)),
        };
        let precinct = match usize::try_from(precinct) {
            Ok(precinct) => precinct,
            Err(_) => return Err(packet_arithmetic_overflow()),
        };
        match start.checked_add(precinct) {
            Some(index) => Ok(index),
            None => Err(packet_arithmetic_overflow()),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_iterator_view(&result) == crate::specs::part1_packet_iterator_initial(packet_grid_view(grid), order),
))]
pub(crate) const fn packet_iterator_new(
    grid: &PacketGrid,
    order: ProgressionOrder,
) -> PacketIterator<'_> {
    PacketIterator {
        grid,
        order,
        candidate_index: 0,
        emitted: 0,
    }
}

impl<'a> PacketIterator<'a> {
    pub const fn new(grid: &'a PacketGrid, order: ProgressionOrder) -> Self {
        packet_iterator_new(grid, order)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == packet_iterator_view(self).emitted,))]
    pub const fn emitted(&self) -> u64 {
        self.emitted
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, packet_iterator_view(final(self))) == crate::specs::part1_packet_iterator_next(packet_iterator_view(old(self))),
    ))]
    pub fn next_packet(&mut self) -> Result<Option<PacketCoordinate>, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_iterator_next); }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant
                    packet_iterator_view(self).grid == packet_iterator_view(old(self)).grid,
                    self.order == old(self).order,
                    crate::specs::part1_packet_iterator_next(packet_iterator_view(old(self)))
                        == crate::specs::part1_packet_iterator_next(packet_iterator_view(self)),
                decreases self.grid.candidate_count as int - self.candidate_index as int,
            )
        )]
        while self.candidate_index < self.grid.candidate_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_packet_iterator_next); }
            let candidate = self.candidate_index;
            self.candidate_index = match self.candidate_index.checked_add(1) {
                Some(index) => index,
                None => return Err(packet_arithmetic_overflow()),
            };
            let coordinate = self.decode_candidate(candidate)?;
            if coordinate.precinct
                < self
                    .grid
                    .precinct_count(coordinate.component, coordinate.resolution)?
            {
                self.emitted = match self.emitted.checked_add(1) {
                    Some(emitted) => emitted,
                    None => return Err(packet_arithmetic_overflow()),
                };
                if self.emitted > self.grid.packet_count {
                    return Err(packet_arithmetic_overflow());
                }
                return Ok(Some(coordinate));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_packet_iterator_next); }
        Ok(None)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_packet_candidate(packet_grid_view(self.grid), self.order, candidate),
    ))]
    fn decode_candidate(&self, candidate: u64) -> Result<PacketCoordinate, DecodeError> {
        let layers = u64::from(self.grid.layers);
        let resolutions = u64::from(self.grid.resolutions);
        let components = u64::from(self.grid.components);
        let precincts = u64::from(self.grid.maximum_precincts_per_resolution);
        let (layer, resolution, component, precinct) = match self.order {
            ProgressionOrder::Lrcp => {
                let values = unravel(candidate, [layers, resolutions, components, precincts])?;
                (values[0], values[1], values[2], values[3])
            }
            ProgressionOrder::Rlcp => {
                let values = unravel(candidate, [resolutions, layers, components, precincts])?;
                (values[1], values[0], values[2], values[3])
            }
            ProgressionOrder::Rpcl => {
                let values = unravel(candidate, [resolutions, precincts, components, layers])?;
                (values[3], values[0], values[2], values[1])
            }
            ProgressionOrder::Pcrl => {
                let values = unravel(candidate, [precincts, components, resolutions, layers])?;
                (values[3], values[2], values[1], values[0])
            }
            ProgressionOrder::Cprl => {
                let values = unravel(candidate, [components, precincts, resolutions, layers])?;
                (values[3], values[2], values[0], values[1])
            }
        };
        Ok(PacketCoordinate {
            layer: match u16::try_from(layer) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            resolution: match u8::try_from(resolution) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            component: match u16::try_from(component) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
            precinct: match u32::try_from(precinct) {
                Ok(value) => value,
                Err(_) => return Err(packet_arithmetic_overflow()),
            },
        })
    }
}

#[cfg(not(verus_keep_ghost))]
impl Iterator for PacketIterator<'_> {
    type Item = Result<PacketCoordinate, DecodeError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_packet().transpose()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures progression_packet_iterator_outcome(result) == crate::specs::part1_progression_iterator_initial(
        packet_grid_view(grid), default_order, crate::codestream::progression_changes_view(changes),
        crate::limits::resource_work_limit(limits)),
))]
pub(crate) fn progression_packet_iterator_new<'a>(
    grid: &'a PacketGrid,
    default_order: ProgressionOrder,
    changes: &'a ProgressionChanges,
    limits: &ResourceLimits,
) -> Result<ProgressionPacketIterator<'a>, DecodeError> {
    let default = if changes.is_empty() {
        Some(packet_iterator_new(grid, default_order))
    } else {
        None
    };
    let mut candidate_work = 0_u64;
    let change_count = changes.records().len();
    let mut index = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_progression_admission); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= change_count,
            change_count == crate::codestream::progression_changes_view(changes).len(),
            crate::specs::part1_progression_admission(packet_grid_view(grid),
                crate::codestream::progression_changes_view(changes),0,0,crate::limits::resource_work_limit(limits))
            == crate::specs::part1_progression_admission(packet_grid_view(grid),
                crate::codestream::progression_changes_view(changes),index,candidate_work,crate::limits::resource_work_limit(limits)),
        decreases change_count-index,
    ))]
    while index < change_count {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_progression_admission); }
        let record = match changes.records().get(index) {
            Some(record) => *record,
            None => {
                return Err(packet_reader_error(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
        };
        candidate_work = match candidate_work.checked_add(window_candidate_count(grid, record)?) {
            Some(work) => work,
            None => return Err(packet_arithmetic_overflow()),
        };
        if candidate_work > limits.maximum_work_units() {
            return Err(packet_reader_limit(
                Resource::WorkUnits,
                limits.maximum_work_units(),
                candidate_work,
            ));
        }
        index = match index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_progression_admission); }
    let window_candidates = match changes.records().first() {
        Some(record) => window_candidate_count(grid, *record)?,
        None => 0,
    };
    Ok(ProgressionPacketIterator {
        grid,
        changes,
        default,
        window_index: 0,
        window_candidate: 0,
        window_candidates,
        emitted: 0,
    })
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<'a> ProgressionPacketIterator<'a> {
    pub fn new(
        grid: &'a PacketGrid,
        default_order: ProgressionOrder,
        changes: &'a ProgressionChanges,
        limits: &ResourceLimits,
    ) -> Result<Self, DecodeError> {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::ensures(|result: Result<Self, DecodeError>| {
            vstd::prelude::equal(
                progression_packet_iterator_outcome(result),
                crate::specs::part1_progression_iterator_initial(
                    packet_grid_view(grid),
                    default_order,
                    crate::codestream::progression_changes_view(changes),
                    crate::limits::resource_work_limit(limits),
                ),
            )
        });
        progression_packet_iterator_new(grid, default_order, changes, limits)
    }
}

impl<'a> ProgressionPacketIterator<'a> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == progression_packet_iterator_view(self).emitted,
    ))]
    pub const fn emitted(&self) -> u64 {
        self.emitted
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, progression_packet_iterator_view(final(self))) ==
            crate::specs::part1_progression_iterator_next(progression_packet_iterator_view(old(self))),
    ))]
    pub fn next_packet(&mut self) -> Result<Option<PacketCoordinate>, DecodeError> {
        let default_step = {
            if let Some(default) = self.default.as_mut() {
                let result = default.next_packet();
                Some((result, default.emitted()))
            } else {
                None
            }
        };
        if let Some((result, emitted)) = default_step {
            let coordinate = result?;
            self.emitted = emitted;
            return Ok(coordinate);
        }
        let change_count = self.changes.records().len();
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_progression_windows_next); }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant change_count == progression_packet_iterator_view(self).changes.len(),
                    self.default.is_none(),
                    crate::specs::part1_progression_iterator_next(progression_packet_iterator_view(old(self)))
                        == crate::specs::part1_progression_windows_next(progression_packet_iterator_view(self)),
                decreases change_count - self.window_index,
            )
        )]
        while self.window_index < change_count {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_progression_windows_next); }
            let record = match self.changes.records().get(self.window_index) {
                Some(record) => *record,
                None => {
                    return Err(packet_reader_error(
                        0,
                        MalformedKind::InvalidProgressionOrderChange,
                    ));
                }
            };
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost initial_window_index = self.window_index; }
            #[cfg_attr(
                verus_keep_ghost,
                verus_spec(
                    invariant change_count == progression_packet_iterator_view(self).changes.len(),
                        self.default.is_none(),
                        self.window_index < change_count,
                        self.window_index == initial_window_index,
                        record == progression_packet_iterator_view(self).changes[self.window_index as int],
                        crate::specs::part1_progression_iterator_next(progression_packet_iterator_view(old(self)))
                            == crate::specs::part1_progression_windows_next(progression_packet_iterator_view(self)),
                    decreases self.window_candidates - self.window_candidate,
                )
            )]
            while self.window_candidate < self.window_candidates {
                #[cfg(verus_keep_ghost)]
                proof! { reveal(crate::specs::part1_progression_windows_next); }
                if let Some(coordinate) = self.candidate_step(record)? {
                    return Ok(Some(coordinate));
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_progression_windows_next); }
            self.next_window()?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_progression_windows_next); }
        if self.emitted != self.grid.packet_count {
            return Err(packet_reader_error(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
        Ok(None)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, progression_packet_iterator_view(final(self))) ==
            crate::specs::part1_progression_candidate_step(progression_packet_iterator_view(old(self)), record),
    ))]
    pub(super) fn candidate_step(
        &mut self,
        record: ProgressionChange,
    ) -> Result<Option<PacketCoordinate>, DecodeError> {
        let candidate = self.window_candidate;
        self.window_candidate = match self.window_candidate.checked_add(1) {
            Some(candidate) => candidate,
            None => return Err(packet_arithmetic_overflow()),
        };
        let coordinate = decode_window_candidate(self.grid, record, candidate)?;
        if coordinate.precinct
            >= self
                .grid
                .precinct_count(coordinate.component, coordinate.resolution)?
        {
            return Ok(None);
        }
        let already_emitted =
            progression_prior_contains(self.changes, self.window_index, coordinate)?;
        if !crate::refinement::progression_emit_allowed(already_emitted) {
            return Ok(None);
        }
        self.emitted = match self.emitted.checked_add(1) {
            Some(emitted) => emitted,
            None => return Err(packet_arithmetic_overflow()),
        };
        if self.emitted > self.grid.packet_count {
            return Err(packet_reader_error(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
        Ok(Some(coordinate))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, progression_packet_iterator_view(final(self))) ==
            crate::specs::part1_progression_next_window(progression_packet_iterator_view(old(self))),
    ))]
    fn next_window(&mut self) -> Result<(), DecodeError> {
        self.window_index = match self.window_index.checked_add(1) {
            Some(index) => index,
            None => return Err(packet_arithmetic_overflow()),
        };
        self.window_candidate = 0;
        self.window_candidates = match self.changes.records().get(self.window_index) {
            Some(next) => window_candidate_count(self.grid, *next)?,
            None => 0,
        };
        Ok(())
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_progression_prior_contains(
        crate::codestream::progression_changes_view(changes),end,0,coordinate),
))]
fn progression_prior_contains(
    changes: &ProgressionChanges,
    end: usize,
    coordinate: PacketCoordinate,
) -> Result<bool, DecodeError> {
    let mut prior = 0_usize;
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_progression_prior_contains); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant prior <= end,
                crate::specs::part1_progression_prior_contains(crate::codestream::progression_changes_view(changes),
                    end,0,coordinate)
                == crate::specs::part1_progression_prior_contains(crate::codestream::progression_changes_view(changes),
                    end,prior,coordinate),
            decreases end-prior,
        ))]
    while prior < end {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_progression_prior_contains); }
        let prior_record = match changes.records().get(prior) {
            Some(record) => *record,
            None => {
                return Err(packet_reader_error(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
        };
        if prior_record.contains(
            coordinate.layer,
            coordinate.resolution,
            coordinate.component,
        ) {
            return Ok(true);
        }
        prior = match prior.checked_add(1) {
            Some(prior) => prior,
            None => return Err(packet_arithmetic_overflow()),
        };
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_progression_prior_contains); }
    Ok(false)
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_window_count(packet_grid_view(grid), record),
))]
pub(super) fn window_candidate_count(
    grid: &PacketGrid,
    record: ProgressionChange,
) -> Result<u64, DecodeError> {
    let resolutions = match record.resolution_end.checked_sub(record.resolution_start) {
        Some(count) => count,
        None => {
            return Err(packet_reader_error(
                0,
                MalformedKind::InvalidProgressionOrderChange,
            ));
        }
    };
    let first = match u64::from(record.layer_end).checked_mul(u64::from(resolutions)) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    let second = match first.checked_mul(u64::from(
        record.component_end.saturating_sub(record.component_start),
    )) {
        Some(count) => count,
        None => return Err(packet_arithmetic_overflow()),
    };
    match second.checked_mul(u64::from(grid.maximum_precincts_per_resolution)) {
        Some(count) => Ok(count),
        None => Err(packet_arithmetic_overflow()),
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crate::specs::part1_packet_window_candidate(packet_grid_view(grid), record, candidate),
))]
pub(super) fn decode_window_candidate(
    grid: &PacketGrid,
    record: ProgressionChange,
    candidate: u64,
) -> Result<PacketCoordinate, DecodeError> {
    let layers = u64::from(record.layer_end);
    let resolutions = u64::from(
        match record.resolution_end.checked_sub(record.resolution_start) {
            Some(count) => count,
            None => {
                return Err(packet_reader_error(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
        },
    );
    let components = u64::from(
        match record.component_end.checked_sub(record.component_start) {
            Some(count) => count,
            None => {
                return Err(packet_reader_error(
                    0,
                    MalformedKind::InvalidProgressionOrderChange,
                ));
            }
        },
    );
    let precincts = u64::from(grid.maximum_precincts_per_resolution);
    let (layer, resolution, component, precinct) = match record.progression_order {
        ProgressionOrder::Lrcp => {
            let values = unravel(candidate, [layers, resolutions, components, precincts])?;
            (values[0], values[1], values[2], values[3])
        }
        ProgressionOrder::Rlcp => {
            let values = unravel(candidate, [resolutions, layers, components, precincts])?;
            (values[1], values[0], values[2], values[3])
        }
        ProgressionOrder::Rpcl => {
            let values = unravel(candidate, [resolutions, precincts, components, layers])?;
            (values[3], values[0], values[2], values[1])
        }
        ProgressionOrder::Pcrl => {
            let values = unravel(candidate, [precincts, components, resolutions, layers])?;
            (values[3], values[2], values[1], values[0])
        }
        ProgressionOrder::Cprl => {
            let values = unravel(candidate, [components, precincts, resolutions, layers])?;
            (values[3], values[2], values[0], values[1])
        }
    };
    Ok(PacketCoordinate {
        layer: match u16::try_from(layer) {
            Ok(value) => value,
            Err(_) => return Err(packet_arithmetic_overflow()),
        },
        resolution: match u8::try_from(resolution) {
            Err(_) => return Err(packet_arithmetic_overflow()),
            Ok(value) => match value.checked_add(record.resolution_start) {
                Some(value) => value,
                None => return Err(packet_arithmetic_overflow()),
            },
        },
        component: match u16::try_from(component) {
            Err(_) => return Err(packet_arithmetic_overflow()),
            Ok(value) => match value.checked_add(record.component_start) {
                Some(value) => value,
                None => return Err(packet_arithmetic_overflow()),
            },
        },
        precinct: match u32::try_from(precinct) {
            Ok(value) => value,
            Err(_) => return Err(packet_arithmetic_overflow()),
        },
    })
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures packet_unravel_outcome(result) == crate::specs::part1_packet_unravel(index, dimensions@),
))]
fn unravel(mut index: u64, dimensions: [u64; 4]) -> Result<[u64; 4], DecodeError> {
    if dimensions[0] == 0 || dimensions[1] == 0 || dimensions[2] == 0 || dimensions[3] == 0 {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    let third = crate::refinement::progression_digit(index, dimensions[3]);
    index = crate::refinement::progression_advance(index, dimensions[3]);
    let second = crate::refinement::progression_digit(index, dimensions[2]);
    index = crate::refinement::progression_advance(index, dimensions[2]);
    let first = crate::refinement::progression_digit(index, dimensions[1]);
    index = crate::refinement::progression_advance(index, dimensions[1]);
    if index >= dimensions[0] {
        return Err(packet_reader_error(0, MalformedKind::InvalidCodingStyle));
    }
    Ok([index, first, second, third])
}
