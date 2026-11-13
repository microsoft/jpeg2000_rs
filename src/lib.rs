#![forbid(unsafe_code)]
#![cfg_attr(verus_keep_ghost, feature(proc_macro_hygiene))]
#![doc = include_str!("../README.md")]

#[cfg(all(verus_keep_ghost, not(feature = "verus")))]
compile_error!(
    "Enable the verification feature: cargo verus verify --features verus -- --no-lifetime"
);

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod allocation;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod error;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod limits;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod options;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
mod refinement;

#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod codestream;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod color;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod decode;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod image;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod jp2;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod jpip;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod jpx;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod magnitude;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod mq;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod packet;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod tier1;
#[cfg_attr(verus_keep_ghost, verifier::verify)]
pub mod transform;

#[cfg(verus_keep_ghost)]
#[path = "../specs/mod.rs"]
mod specs;

#[cfg(verus_keep_ghost)]
#[path = "../proofs/mod.rs"]
mod proofs;

pub use color::{
    ConvertedChannel, ConvertedChannelType, ConvertedColorSpace, ConvertedImage, convert_jp2_color,
};
pub use decode::{
    decode_codestream, decode_codestream_reconstructed, decode_codestream_selected, decode_jp2,
    decode_jp2_color, decode_jp2_color_selected, decode_jp2_selected, decode_jph, decode_jph_color,
    decode_jph_color_selected, decode_jph_selected, decode_jpx_codestream,
    decode_jpx_codestream_color, decode_jpx_codestream_color_selected,
    decode_jpx_codestream_selected,
};
pub use error::{
    DecodeError, IoKind, JpipMappingAmbiguity, MalformedKind, Resource, SelectionError,
    UnsupportedColorConversion,
};
pub use image::{
    ChannelAssociation, ChannelDefinition, ChannelType, TypedComponent, TypedImage, TypedSamples,
};
pub use jp2::inspect_jph;
pub use jpip::{
    DatabinCache, DatabinClass, DatabinId, DatabinStatus, JpipAutomaticProgressiveDecoder,
    JpipAvailability, JpipAvailabilityReport, JpipByteView, JpipContainerAssembly,
    JpipDatabinRange, JpipEndOfResponse, JpipFragment, JpipHeaderContext, JpipMessage,
    JpipMessageHeader, JpipMessageParser, JpipMissingRange, JpipPacketSelection,
    JpipPrecinctCodestreamPlan, JpipPrecinctCoordinate, JpipPrecinctMap, JpipPrecinctMapping,
    JpipPrecinctPacket, JpipPrecinctPackets, JpipPrecinctTranscode, JpipProgressiveDecoder,
    JpipProgressiveStatus, JpipProgressiveUpdate, JpipResponseSummary, JpipSemanticNeed,
    JpipSemanticNeedKind, JpipTilePartTransition, JpipTilePartTransitionReport,
    ingest_jpip_response, parse_jpip_message,
};
pub use jpx::{
    JpxCompositionInfo, JpxFrameInfo, JpxInspection, JpxInstructionInfo, JpxLayerInfo,
    inspect_jpx_layers, render_jpx_composition, render_jpx_frame, render_jpx_layer,
};
pub use limits::ResourceLimits;
pub use options::{DecodeOptions, DecodeSelection, ImageRegion, TileSelection};
