use crate::{DecodeError, Resource};

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
pub struct ResourceLimits {
    maximum_input_bytes: u64,
    maximum_metadata_bytes: u64,
    maximum_box_depth: u32,
    maximum_compatible_brands: u32,
    maximum_codestreams: u32,
    maximum_width: u32,
    maximum_height: u32,
    maximum_pixels: u64,
    maximum_components: u16,
    maximum_tiles: u32,
    maximum_tile_parts: u32,
    maximum_resolutions_per_component: u8,
    maximum_precincts: u64,
    maximum_code_blocks: u64,
    maximum_code_block_passes: u32,
    maximum_code_block_bytes: u64,
    maximum_layers: u16,
    maximum_frames: u32,
    maximum_packets: u64,
    maximum_packet_header_bytes: u64,
    maximum_decoded_bytes: u64,
    maximum_jpip_fragments: u64,
    maximum_tag_tree_nodes: u64,
    maximum_work_units: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn resource_input_byte_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_input_bytes
    }

    pub closed spec fn resource_metadata_byte_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_metadata_bytes
    }

    pub closed spec fn resource_work_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_work_units
    }

    pub closed spec fn resource_code_block_byte_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_code_block_bytes
    }

    pub closed spec fn resource_code_block_pass_limit(limits: &ResourceLimits) -> u32 {
        limits.maximum_code_block_passes
    }

    pub closed spec fn resource_decoded_bytes_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_decoded_bytes
    }

    pub closed spec fn resource_packet_header_byte_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_packet_header_bytes
    }

    pub closed spec fn resource_tag_tree_node_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_tag_tree_nodes
    }

    pub closed spec fn resource_packet_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_packets
    }

    pub closed spec fn resource_jpip_fragment_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_jpip_fragments
    }

    pub closed spec fn resource_precinct_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_precincts
    }

    pub closed spec fn resource_code_block_limit(limits: &ResourceLimits) -> u64 {
        limits.maximum_code_blocks
    }

    pub closed spec fn resource_component_limit(limits: &ResourceLimits) -> u16 {
        limits.maximum_components
    }

    pub closed spec fn resource_width_limit(limits: &ResourceLimits) -> u32 { limits.maximum_width }
    pub closed spec fn resource_height_limit(limits: &ResourceLimits) -> u32 { limits.maximum_height }
    pub closed spec fn resource_pixel_limit(limits: &ResourceLimits) -> u64 { limits.maximum_pixels }
    pub closed spec fn resource_frame_limit(limits: &ResourceLimits) -> u32 { limits.maximum_frames }
    pub closed spec fn resource_compatible_brand_limit(limits: &ResourceLimits) -> u32 { limits.maximum_compatible_brands }
    pub closed spec fn resource_box_depth_limit(limits: &ResourceLimits) -> u32 { limits.maximum_box_depth }
    pub closed spec fn resource_codestream_limit(limits: &ResourceLimits) -> u32 { limits.maximum_codestreams }
    pub closed spec fn resource_tile_limit(limits: &ResourceLimits) -> u32 { limits.maximum_tiles }

    pub closed spec fn resource_tile_part_limit(limits: &ResourceLimits) -> u32 {
        limits.maximum_tile_parts
    }

    pub closed spec fn resource_resolution_limit(limits: &ResourceLimits) -> u8 {
        limits.maximum_resolutions_per_component
    }

    pub closed spec fn resource_layer_limit(limits: &ResourceLimits) -> u16 {
        limits.maximum_layers
    }
}

impl ResourceLimits {
    #[cfg(test)]
    pub(crate) fn with_coding_style_limits_for_test(
        mut self,
        layers: u16,
        resolutions: u8,
    ) -> Self {
        self.maximum_layers = layers;
        self.maximum_resolutions_per_component = resolutions;
        self
    }

    #[cfg(test)]
    pub(crate) fn with_geometry_limits_for_test(
        mut self,
        components: u16,
        width: u32,
        height: u32,
        pixels: u64,
        tiles: u32,
    ) -> Self {
        self.maximum_components = components;
        self.maximum_width = width;
        self.maximum_height = height;
        self.maximum_pixels = pixels;
        self.maximum_tiles = tiles;
        self
    }

    pub const HARDENED: Self = Self {
        maximum_input_bytes: 2_147_483_648,
        maximum_metadata_bytes: 16_777_216,
        maximum_box_depth: 32,
        maximum_compatible_brands: 64,
        maximum_codestreams: 64,
        maximum_width: 1_000_000,
        maximum_height: 1_000_000,
        maximum_pixels: 100_000_000,
        maximum_components: 64,
        maximum_tiles: 16_384,
        maximum_tile_parts: 16_384,
        maximum_resolutions_per_component: 33,
        maximum_precincts: 16_777_216,
        maximum_code_blocks: 16_777_216,
        maximum_code_block_passes: crate::tier1::MAX_TIER1_PASSES,
        maximum_code_block_bytes: 67_580,
        maximum_layers: 256,
        maximum_frames: 4_096,
        maximum_packets: 67_108_864,
        maximum_packet_header_bytes: 268_435_456,
        maximum_decoded_bytes: 2_147_483_648,
        maximum_jpip_fragments: 1_048_576,
        maximum_tag_tree_nodes: 16_777_216,
        maximum_work_units: 1_000_000_000,
    };

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == resource_input_byte_limit(self),)
    )]
    pub const fn maximum_input_bytes(&self) -> u64 {
        self.maximum_input_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == crate::specs::part1_metadata_byte_limit(self),))]
    pub const fn maximum_metadata_bytes(&self) -> u64 {
        self.maximum_metadata_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_box_depth_limit(self),))]
    pub const fn maximum_box_depth(&self) -> u32 {
        self.maximum_box_depth
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_compatible_brand_limit(self),))]
    pub const fn maximum_compatible_brands(&self) -> u32 {
        self.maximum_compatible_brands
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_codestream_limit(self),))]
    pub const fn maximum_codestreams(&self) -> u32 {
        self.maximum_codestreams
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == resource_width_limit(self),))]
    pub const fn maximum_width(&self) -> u32 {
        self.maximum_width
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == resource_height_limit(self),))]
    pub const fn maximum_height(&self) -> u32 {
        self.maximum_height
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == resource_pixel_limit(self),))]
    pub const fn maximum_pixels(&self) -> u64 {
        self.maximum_pixels
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        ensures value == resource_component_limit(self),
    ))]
    pub const fn maximum_components(&self) -> u16 {
        self.maximum_components
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == resource_tile_limit(self),))]
    pub const fn maximum_tiles(&self) -> u32 {
        self.maximum_tiles
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_tile_part_limit(self),))]
    pub const fn maximum_tile_parts(&self) -> u32 {
        self.maximum_tile_parts
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_resolution_limit(self),))]
    pub const fn maximum_resolutions_per_component(&self) -> u8 {
        self.maximum_resolutions_per_component
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_precinct_limit(self),))]
    pub const fn maximum_precincts(&self) -> u64 {
        self.maximum_precincts
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_code_block_limit(self),))]
    pub const fn maximum_code_blocks(&self) -> u64 {
        self.maximum_code_blocks
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == resource_code_block_pass_limit(self),)
    )]
    pub const fn maximum_code_block_passes(&self) -> u32 {
        self.maximum_code_block_passes
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == resource_code_block_byte_limit(self),)
    )]
    pub const fn maximum_code_block_bytes(&self) -> u64 {
        self.maximum_code_block_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_layer_limit(self),))]
    pub const fn maximum_layers(&self) -> u16 {
        self.maximum_layers
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_frame_limit(self),))]
    pub const fn maximum_frames(&self) -> u32 {
        self.maximum_frames
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_packet_limit(self),))]
    pub const fn maximum_packets(&self) -> u64 {
        self.maximum_packets
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_packet_header_byte_limit(self),))]
    pub const fn maximum_packet_header_bytes(&self) -> u64 {
        self.maximum_packet_header_bytes
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == resource_decoded_bytes_limit(self),)
    )]
    pub const fn maximum_decoded_bytes(&self) -> u64 {
        self.maximum_decoded_bytes
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_jpip_fragment_limit(self),))]
    pub const fn maximum_jpip_fragments(&self) -> u64 {
        self.maximum_jpip_fragments
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == resource_tag_tree_node_limit(self),))]
    pub const fn maximum_tag_tree_nodes(&self) -> u64 {
        self.maximum_tag_tree_nodes
    }

    #[cfg_attr(
        verus_keep_ghost,
        verus_spec(value => ensures value == resource_work_limit(self),)
    )]
    pub const fn maximum_work_units(&self) -> u64 {
        self.maximum_work_units
    }

    pub fn with_maximum_input_bytes(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::InputBytes,
            Self::HARDENED.maximum_input_bytes,
            value,
        )?;
        let mut updated = self;
        updated.maximum_input_bytes = value;
        Ok(updated)
    }

    pub fn with_maximum_metadata_bytes(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::MetadataBytes,
            Self::HARDENED.maximum_metadata_bytes,
            value,
        )?;
        let mut updated = self;
        updated.maximum_metadata_bytes = value;
        Ok(updated)
    }

    pub fn with_maximum_codestreams(self, value: u32) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::Codestreams,
            u64::from(Self::HARDENED.maximum_codestreams),
            u64::from(value),
        )?;
        let mut updated = self;
        updated.maximum_codestreams = value;
        Ok(updated)
    }

    pub fn with_maximum_compatible_brands(self, value: u32) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::CompatibleBrands,
            u64::from(Self::HARDENED.maximum_compatible_brands),
            u64::from(value),
        )?;
        let mut updated = self;
        updated.maximum_compatible_brands = value;
        Ok(updated)
    }

    pub fn with_maximum_tile_parts(self, value: u32) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::TileParts,
            u64::from(Self::HARDENED.maximum_tile_parts),
            u64::from(value),
        )?;
        let mut updated = self;
        updated.maximum_tile_parts = value;
        Ok(updated)
    }

    pub fn with_maximum_packet_header_bytes(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::PacketHeaderBytes,
            Self::HARDENED.maximum_packet_header_bytes,
            value,
        )?;
        let mut updated = self;
        updated.maximum_packet_header_bytes = value;
        Ok(updated)
    }

    pub fn with_maximum_packets(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(Resource::Packets, Self::HARDENED.maximum_packets, value)?;
        let mut updated = self;
        updated.maximum_packets = value;
        Ok(updated)
    }

    pub fn with_maximum_code_blocks(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::CodeBlocks,
            Self::HARDENED.maximum_code_blocks,
            value,
        )?;
        let mut updated = self;
        updated.maximum_code_blocks = value;
        Ok(updated)
    }

    pub fn with_maximum_code_block_passes(self, value: u32) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::CodeBlockPasses,
            u64::from(Self::HARDENED.maximum_code_block_passes),
            u64::from(value),
        )?;
        let mut updated = self;
        updated.maximum_code_block_passes = value;
        Ok(updated)
    }

    pub fn with_maximum_code_block_bytes(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::CodeBlockBytes,
            Self::HARDENED.maximum_code_block_bytes,
            value,
        )?;
        let mut updated = self;
        updated.maximum_code_block_bytes = value;
        Ok(updated)
    }

    pub fn with_maximum_decoded_bytes(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::DecodedBytes,
            Self::HARDENED.maximum_decoded_bytes,
            value,
        )?;
        let mut updated = self;
        updated.maximum_decoded_bytes = value;
        Ok(updated)
    }

    pub fn with_maximum_frames(self, value: u32) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::Frames,
            u64::from(Self::HARDENED.maximum_frames),
            u64::from(value),
        )?;
        let mut updated = self;
        updated.maximum_frames = value;
        Ok(updated)
    }

    pub fn with_maximum_jpip_fragments(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::JpipFragments,
            Self::HARDENED.maximum_jpip_fragments,
            value,
        )?;
        let mut updated = self;
        updated.maximum_jpip_fragments = value;
        Ok(updated)
    }

    pub fn with_maximum_work_units(self, value: u64) -> Result<Self, DecodeError> {
        Self::ensure_tightened(
            Resource::WorkUnits,
            Self::HARDENED.maximum_work_units,
            value,
        )?;
        let mut updated = self;
        updated.maximum_work_units = value;
        Ok(updated)
    }

    fn ensure_tightened(resource: Resource, hard: u64, requested: u64) -> Result<(), DecodeError> {
        if requested <= hard {
            Ok(())
        } else {
            Err(DecodeError::limit(resource, hard, requested))
        }
    }
}

impl Default for ResourceLimits {
    fn default() -> Self {
        Self::HARDENED
    }
}
