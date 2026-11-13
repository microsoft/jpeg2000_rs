//! Part 2 extension accessors, selectors and owned metadata copies.

use super::{
    ArbitraryDecomposition, ArbitraryKernel, ComponentBitDepth, ComponentRegistration, DecodeError,
    DecompositionDirection, DecompositionStructure, KernelCoefficient, KernelLiftingStep,
    NonlinearPointTransform, Part2Extensions, TilePartLength,
};
#[cfg(verus_keep_ghost)]
use super::{
    ads_option_view, component_depth_views, dfs_option_view, nonlinear_transform_option_view,
    owned_arbitrary_decomposition_view, owned_decomposition_view, owned_extensions_view,
    owned_kernel_view, owned_nonlinear_list_view, owned_nonlinear_view, part2_component_depths,
    part2_execution_registry, part2_kernel_registry, raw_kernel_coefficient_option,
    raw_kernel_coefficient_view, raw_kernel_coefficients_view, raw_kernel_step_view,
    raw_kernel_steps_view, raw_kernel_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures owned_extensions_view(&result) == crate::specs::part1_empty_extensions(),
))]
pub(super) const fn new_part2_extensions() -> Part2Extensions {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(owned_extensions_view); }
    let result = Part2Extensions {
        decomposition_structures: Vec::new(),
        arbitrary_decompositions: Vec::new(),
        nonlinear_transforms: Vec::new(),
        nonlinear_local_count: None,
        component_bit_depths: Vec::new(),
        arbitrary_kernels: Vec::new(),
        component_registrations: Vec::new(),
        tile_part_lengths: Vec::new(),
        metadata_bytes: 0,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let actual = owned_extensions_view(&result);
        assert(actual.decompositions =~= Seq::empty());
        assert(actual.arbitrary =~= Seq::empty());
        assert(actual.nonlinear =~= Seq::empty());
        assert(actual.depths =~= Seq::empty());
        assert(actual.kernels =~= Seq::empty());
        assert(actual.registrations =~= Seq::empty());
        assert(actual.lengths =~= Seq::empty());
    }
    result
}

impl Default for Part2Extensions {
    fn default() -> Self {
        new_part2_extensions()
    }
}

impl DecompositionStructure {
    pub const fn index(&self) -> u8 {
        self.index
    }

    pub fn directions(&self) -> &[DecompositionDirection] {
        &self.directions
    }
}
impl ArbitraryDecomposition {
    pub const fn index(&self) -> u8 {
        self.index
    }

    pub fn sublevel_depths(&self) -> &[u8] {
        &self.sublevel_depths
    }

    pub fn subband_splits(&self) -> &[DecompositionDirection] {
        &self.subband_splits
    }
}
impl NonlinearPointTransform {
    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).component,))]
    pub const fn component(&self) -> Option<u16> {
        self.component
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).precision,))]
    pub const fn precision(&self) -> u8 {
        self.precision
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).signed,))]
    pub const fn signed(&self) -> bool {
        self.signed
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).transform_type,))]
    pub const fn transform_type(&self) -> u8 {
        self.transform_type
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value@ == owned_nonlinear_view(self).parameters,))]
    pub fn parameters(&self) -> &[u8] {
        &self.parameters
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).d_min,))]
    pub const fn d_min(&self) -> Option<u32> {
        self.d_min
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).d_max,))]
    pub const fn d_max(&self) -> Option<u32> {
        self.d_max
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).point_bits,))]
    pub const fn point_bits(&self) -> Option<u8> {
        self.point_bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value@ == owned_nonlinear_view(self).points,))]
    pub fn points(&self) -> &[u32] {
        &self.points
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == owned_nonlinear_view(self).gamma,))]
    pub const fn gamma_parameters(&self) -> Option<[u32; 5]> {
        self.gamma_parameters
    }

    #[cfg(test)]
    pub(crate) fn for_test(
        precision: u8,
        signed: bool,
        transform_type: u8,
        d_min: Option<u32>,
        d_max: Option<u32>,
        points: Vec<u32>,
    ) -> Self {
        Self {
            component: None,
            precision,
            signed,
            transform_type,
            parameters: Vec::new(),
            d_min,
            d_max,
            point_bits: None,
            points,
            gamma_parameters: None,
        }
    }

    #[cfg(test)]
    pub(crate) fn gamma_for_test(precision: u8, signed: bool, parameters: [u32; 5]) -> Self {
        Self {
            component: None,
            precision,
            signed,
            transform_type: 1,
            parameters: Vec::new(),
            d_min: None,
            d_max: None,
            point_bits: None,
            points: Vec::new(),
            gamma_parameters: Some(parameters),
        }
    }
}
impl KernelCoefficient {
    #[cfg(test)]
    pub(crate) fn for_test(bits: u128, width: u8) -> Self {
        Self {
            bytes: bits.to_be_bytes(),
            width,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result@ == raw_kernel_coefficient_view(*self).0,
    ))]
    pub const fn bytes(&self) -> &[u8; 16] {
        &self.bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_coefficient_view(*self).1,
    ))]
    pub const fn width(&self) -> u8 {
        self.width
    }
}
impl KernelLiftingStep {
    #[cfg(test)]
    pub(crate) fn for_test(
        offset: i8,
        exponent: u8,
        residue: Option<KernelCoefficient>,
        coefficients: Vec<KernelCoefficient>,
    ) -> Self {
        Self {
            offset,
            exponent,
            residue,
            coefficients,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_step_view(*self).0,
    ))]
    pub const fn offset(&self) -> i8 {
        self.offset
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_step_view(*self).1,
    ))]
    pub const fn exponent(&self) -> u8 {
        self.exponent
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures raw_kernel_coefficient_option(result) == raw_kernel_step_view(*self).2,
    ))]
    pub const fn residue(&self) -> Option<KernelCoefficient> {
        self.residue
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures raw_kernel_coefficients_view(result@) == raw_kernel_step_view(*self).3,
    ))]
    pub fn coefficients(&self) -> &[KernelCoefficient] {
        &self.coefficients
    }
}
impl ArbitraryKernel {
    #[cfg(test)]
    pub(crate) fn for_test(
        reversible: bool,
        coefficient_type: u8,
        whole_sample_filter: bool,
        initial_odd: bool,
        whole_sample_extension: bool,
        scaling: Option<KernelCoefficient>,
        steps: Vec<KernelLiftingStep>,
    ) -> Self {
        Self {
            index: u8::MAX,
            reversible,
            descriptor: u16::MAX,
            coefficient_type,
            whole_sample_filter,
            initial_odd,
            whole_sample_extension,
            scaling,
            steps,
        }
    }

    pub const fn index(&self) -> u8 {
        self.index
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_view(*self).0,
    ))]
    pub const fn reversible(&self) -> bool {
        self.reversible
    }

    pub const fn descriptor(&self) -> u16 {
        self.descriptor
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_view(*self).1,
    ))]
    pub const fn coefficient_type(&self) -> u8 {
        self.coefficient_type
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_view(*self).2,
    ))]
    pub const fn whole_sample_filter(&self) -> bool {
        self.whole_sample_filter
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_view(*self).3,
    ))]
    pub const fn initial_odd(&self) -> bool {
        self.initial_odd
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == raw_kernel_view(*self).4,
    ))]
    pub const fn whole_sample_extension(&self) -> bool {
        self.whole_sample_extension
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures raw_kernel_coefficient_option(result) == raw_kernel_view(*self).5,
    ))]
    pub const fn scaling(&self) -> Option<KernelCoefficient> {
        self.scaling
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures raw_kernel_steps_view(result@) == raw_kernel_view(*self).6,
    ))]
    pub fn steps(&self) -> &[KernelLiftingStep] {
        &self.steps
    }
}
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures nonlinear_transform_option_view(result) == crate::specs::part2_nonlinear_transform_for_unscoped(
        owned_nonlinear_list_view(transforms@), component,
    ),
))]
fn find_nonlinear_transform(
    transforms: &[NonlinearPointTransform],
    component: u16,
) -> Option<&NonlinearPointTransform> {
    let mut position = 0_usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= transforms.len(),
            crate::specs::part2_nonlinear_find(owned_nonlinear_list_view(transforms@), Some(component), 0)
                == crate::specs::part2_nonlinear_find(owned_nonlinear_list_view(transforms@), Some(component), position as nat),
        decreases transforms.len() - position,
    ))]
    while position < transforms.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nonlinear_find, 1); }
        let transform = &transforms[position];
        if transform.component == Some(component) {
            return Some(transform);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nonlinear_find, 1); }
    position = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant position <= transforms.len(),
            crate::specs::part2_nonlinear_find(owned_nonlinear_list_view(transforms@), Some(component), 0) == None,
            crate::specs::part2_nonlinear_find(owned_nonlinear_list_view(transforms@), None, 0)
                == crate::specs::part2_nonlinear_find(owned_nonlinear_list_view(transforms@), None, position as nat),
        decreases transforms.len() - position,
    ))]
    while position < transforms.len() {
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(crate::specs::part2_nonlinear_find, 1); }
        let transform = &transforms[position];
        if transform.component.is_none() {
            return Some(transform);
        }
        position += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal_with_fuel(crate::specs::part2_nonlinear_find, 1); }
    None
}

impl Part2Extensions {
    pub fn decomposition_structures(&self) -> &[DecompositionStructure] {
        &self.decomposition_structures
    }

    pub fn arbitrary_decompositions(&self) -> &[ArbitraryDecomposition] {
        &self.arbitrary_decompositions
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.len() == owned_extensions_view(self).nonlinear.len(),
    ))]
    pub fn nonlinear_transforms(&self) -> &[NonlinearPointTransform] {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_extensions_view); reveal(owned_nonlinear_list_view); }
        &self.nonlinear_transforms
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures component_depth_views(result@) == part2_component_depths(self),
    ))]
    pub fn component_bit_depths(&self) -> &[ComponentBitDepth] {
        &self.component_bit_depths
    }

    pub fn arbitrary_kernels(&self) -> &[ArbitraryKernel] {
        &self.arbitrary_kernels
    }

    pub fn component_registrations(&self) -> &[ComponentRegistration] {
        &self.component_registrations
    }

    pub fn tile_part_lengths(&self) -> &[TilePartLength] {
        &self.tile_part_lengths
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures nonlinear_transform_option_view(result) == crate::specs::part2_nonlinear_transform_for(
            owned_extensions_view(self).nonlinear, component, owned_extensions_view(self).nonlinear_local_count,
        ),
    ))]
    pub(crate) fn nonlinear_transform_for(
        &self,
        component: u16,
    ) -> Option<&NonlinearPointTransform> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_extensions_view); reveal(owned_nonlinear_list_view); }
        let length = self.nonlinear_transforms.len();
        let split = self.nonlinear_local_count.unwrap_or(length).min(length);
        let local = &self.nonlinear_transforms[..split];
        let inherited = &self.nonlinear_transforms[split..];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(owned_nonlinear_list_view(local@) =~= owned_extensions_view(self).nonlinear.take(split as int));
            assert(owned_nonlinear_list_view(inherited@) =~= owned_extensions_view(self).nonlinear.skip(split as int));
        }
        if let Some(transform) = find_nonlinear_transform(local, component) {
            return Some(transform);
        }
        find_nonlinear_transform(inherited, component)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures dfs_option_view(result) == crate::specs::part1_dfs_lookup(owned_extensions_view(self).decompositions, index, 0),
            result.is_some() == part2_execution_registry(self).0.contains(index),
    ))]
    pub(crate) fn decomposition_structure(&self, index: u8) -> Option<&DecompositionStructure> {
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.decomposition_structures.len(),
                crate::specs::part1_dfs_lookup(owned_extensions_view(self).decompositions, index, 0)
                    == crate::specs::part1_dfs_lookup(owned_extensions_view(self).decompositions, index, position as nat),
                forall|prior: int| 0 <= prior < position ==> self.decomposition_structures@[prior].index != index,
            decreases self.decomposition_structures.len() - position,
        ))]
        while position < self.decomposition_structures.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_dfs_lookup, 1); }
            let structure = &self.decomposition_structures[position];
            if structure.index == index {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(part2_execution_registry(self).0[position as int] == index);
                    assert(part2_execution_registry(self).0.contains(index));
                }
                return Some(structure);
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_dfs_lookup, 1);
            if part2_execution_registry(self).0.contains(index) {
                let prior = choose|prior: int| 0 <= prior < part2_execution_registry(self).0.len()
                    && part2_execution_registry(self).0[prior] == index;
                assert(self.decomposition_structures@[prior].index != index);
                assert(false);
            }
        }
        None
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures crate::transform::arbitrary_kernel_option(result)
            == crate::specs::part2_kernel_registry_lookup(part2_kernel_registry(self), index),
    ))]
    pub(crate) fn arbitrary_kernel(&self, index: u8) -> Option<&ArbitraryKernel> {
        #[cfg(verus_keep_ghost)]
        proof! { crate::proofs::production_impl::production_kernel_registry_empty(part2_kernel_registry(self), index); }
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.arbitrary_kernels.len(),
            crate::specs::part2_kernel_registry_prefix(part2_kernel_registry(self), index, position as nat) == None,
            decreases self.arbitrary_kernels.len() - position,
        ))]
        while position < self.arbitrary_kernels.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::proofs::production_impl::production_kernel_registry_step(part2_kernel_registry(self), index, position as nat);
                crate::proofs::production_impl::production_kernel_registry_found(part2_kernel_registry(self), index, position as nat + 1, self.arbitrary_kernels@.len());
            }
            let kernel = &self.arbitrary_kernels[position];
            if kernel.index == index {
                return Some(kernel);
            }
            position += 1;
        }
        None
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures ads_option_view(result) == crate::specs::part1_ads_lookup(owned_extensions_view(self).arbitrary, index, 0),
            result.is_some() == part2_execution_registry(self).1.contains(index),
    ))]
    pub(crate) fn arbitrary_decomposition(&self, index: u8) -> Option<&ArbitraryDecomposition> {
        let mut position = 0_usize;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant position <= self.arbitrary_decompositions.len(),
                crate::specs::part1_ads_lookup(owned_extensions_view(self).arbitrary, index, 0)
                    == crate::specs::part1_ads_lookup(owned_extensions_view(self).arbitrary, index, position as nat),
                forall|prior: int| 0 <= prior < position ==> self.arbitrary_decompositions@[prior].index != index,
            decreases self.arbitrary_decompositions.len() - position,
        ))]
        while position < self.arbitrary_decompositions.len() {
            #[cfg(verus_keep_ghost)]
            proof! { reveal_with_fuel(crate::specs::part1_ads_lookup, 1); }
            let decomposition = &self.arbitrary_decompositions[position];
            if decomposition.index == index {
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(part2_execution_registry(self).1[position as int] == index);
                    assert(part2_execution_registry(self).1.contains(index));
                }
                return Some(decomposition);
            }
            position += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal_with_fuel(crate::specs::part1_ads_lookup, 1);
            if part2_execution_registry(self).1.contains(index) {
                let prior = choose|prior: int| 0 <= prior < part2_execution_registry(self).1.len()
                    && part2_execution_registry(self).1[prior] == index;
                assert(self.arbitrary_decompositions@[prior].index != index);
                assert(false);
            }
        }
        None
    }

    #[cfg(test)]
    pub(crate) fn with_nonlinear_transform_for_test(transform: NonlinearPointTransform) -> Self {
        Self {
            nonlinear_transforms: vec![transform],
            ..Self::default()
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part2_component_depths_equal(part2_component_depths(self), part2_component_depths(other)),
    ))]
    pub(crate) fn component_bit_depths_equal(&self, other: &Self) -> bool {
        if self.component_bit_depths.len() != other.component_bit_depths.len() {
            return false;
        }
        let mut index = 0_usize;
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant index <= self.component_bit_depths.len(),
                    self.component_bit_depths.len() == other.component_bit_depths.len(),
                    forall|position: int| 0 <= position < index ==>
                        part2_component_depths(self)[position] == part2_component_depths(other)[position],
                decreases self.component_bit_depths.len() - index,
            )
        )]
        while index < self.component_bit_depths.len() {
            let Some(left) = self.component_bit_depths.get(index) else {
                return false;
            };
            let Some(right) = other.component_bit_depths.get(index) else {
                return false;
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(part2_component_depths(self)[index as int] == (left.precision, left.signed));
                assert(part2_component_depths(other)[index as int] == (right.precision, right.signed));
            }
            if left.precision != right.precision || left.signed != right.signed {
                #[cfg(verus_keep_ghost)]
                proof! { assert(part2_component_depths(self) != part2_component_depths(other)); }
                return false;
            }
            index += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(part2_component_depths(self) =~= part2_component_depths(other)); }
        true
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Ok(()),))]
    pub(crate) fn validate_executable(&self) -> Result<(), DecodeError> {
        Ok(())
    }
}
impl Clone for DecompositionStructure {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures owned_decomposition_view(&result) == owned_decomposition_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_decomposition_view); }
        Self {
            index: self.index,
            directions: self.directions.clone(),
        }
    }
}
impl Clone for ArbitraryDecomposition {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures owned_arbitrary_decomposition_view(&result) == owned_arbitrary_decomposition_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_arbitrary_decomposition_view); }
        Self {
            index: self.index,
            sublevel_depths: self.sublevel_depths.clone(),
            subband_splits: self.subband_splits.clone(),
        }
    }
}
impl Clone for NonlinearPointTransform {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures owned_nonlinear_view(&result) == owned_nonlinear_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_nonlinear_view); }
        Self {
            component: self.component,
            precision: self.precision,
            signed: self.signed,
            transform_type: self.transform_type,
            parameters: self.parameters.clone(),
            d_min: self.d_min,
            d_max: self.d_max,
            point_bits: self.point_bits,
            points: self.points.clone(),
            gamma_parameters: self.gamma_parameters,
        }
    }
}
impl Clone for KernelLiftingStep {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures raw_kernel_step_view(result) == raw_kernel_step_view(*self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(raw_kernel_step_view); }
        Self {
            offset: self.offset,
            exponent: self.exponent,
            residue: self.residue,
            coefficients: self.coefficients.clone(),
        }
    }
}
impl Clone for ArbitraryKernel {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures owned_kernel_view(&result) == owned_kernel_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_kernel_view); reveal(raw_kernel_view); }
        Self {
            index: self.index,
            reversible: self.reversible,
            descriptor: self.descriptor,
            coefficient_type: self.coefficient_type,
            whole_sample_filter: self.whole_sample_filter,
            initial_odd: self.initial_odd,
            whole_sample_extension: self.whole_sample_extension,
            scaling: self.scaling,
            steps: self.steps.clone(),
        }
    }
}
impl Clone for Part2Extensions {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures owned_extensions_view(&result) == owned_extensions_view(self),))]
    fn clone(&self) -> Self {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(owned_extensions_view); }
        let copied = Self {
            decomposition_structures: self.decomposition_structures.clone(),
            arbitrary_decompositions: self.arbitrary_decompositions.clone(),
            nonlinear_transforms: self.nonlinear_transforms.clone(),
            nonlinear_local_count: self.nonlinear_local_count,
            component_bit_depths: self.component_bit_depths.clone(),
            arbitrary_kernels: self.arbitrary_kernels.clone(),
            component_registrations: self.component_registrations.clone(),
            tile_part_lengths: self.tile_part_lengths.clone(),
            metadata_bytes: self.metadata_bytes,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let a = owned_extensions_view(&copied);
            let b = owned_extensions_view(self);
            assert(a.decompositions =~= b.decompositions);
            assert(a.arbitrary =~= b.arbitrary);
            assert(a.nonlinear =~= b.nonlinear);
            assert(a.depths =~= b.depths);
            assert(a.kernels =~= b.kernels);
            assert(a.registrations =~= b.registrations);
            assert(a.lengths =~= b.lengths);
        }
        copied
    }
}
