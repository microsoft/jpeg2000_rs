#[cfg(not(verus_keep_ghost))]
use core::fmt;
#[cfg(verus_keep_ghost)]
use vstd::prelude::verus_spec;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum IoKind {
    NotFound,
    PermissionDenied,
    UnexpectedEof,
    Interrupted,
    Other,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum MalformedKind {
    Truncated,
    InvalidBoxLength,
    InvalidBoxOrder,
    InvalidBoxContents,
    InvalidFileType,
    InvalidColorSpecification,
    InvalidChannelLayout,
    InvalidAlphaAssociation,
    InvalidSignature,
    InvalidMarker,
    InvalidMarkerLength,
    InvalidMarkerOrder,
    InvalidProfile,
    InvalidImageGeometry,
    InvalidCodingStyle,
    InvalidProgressionOrderChange,
    InvalidQuantization,
    InvalidRegionOfInterest,
    InvalidBitStuffing,
    InvalidTagTree,
    InvalidPacketHeader,
    InvalidPackedPacketHeader,
    InvalidPacketLength,
    InvalidJpipHeader,
    InvalidJpipVbas,
    InvalidJpipFragment,
    InvalidJpipLayout,
    ConflictingJpipFragment,
    InvalidMqState,
    InvalidCodeBlock,
    InvalidTransform,
    InvalidTilePart,
    ContainerCodestreamMismatch,
    MissingRequiredStructure,
    TrailingData,
    ArithmeticOverflow,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum Resource {
    InputBytes,
    MetadataBytes,
    BoxDepth,
    CompatibleBrands,
    Codestreams,
    Width,
    Height,
    Pixels,
    Components,
    TransformElements,
    Tiles,
    TileParts,
    Resolutions,
    Precincts,
    CodeBlocks,
    CodeBlockPasses,
    CodeBlockBytes,
    Layers,
    Frames,
    Packets,
    PacketHeaderBytes,
    DecodedBytes,
    JpipFragments,
    TagTreeNodes,
    WorkUnits,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum UnsupportedColorConversion {
    IccProfile,
    EnumeratedColorSpace,
    ChannelLayout,
    AlphaAssociation,
    /// Component samples have no specified colour space to convert.
    UnspecifiedColorSpace,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum SelectionError {
    EmptyTileSet,
    DuplicateTile,
    TileOutOfRange,
    NonRectangularTileSet,
    EmptyRegion,
    RegionOutOfBounds,
    RegionOutsideSelectedTiles,
    ReductionTooLarge,
    EmptyComponentIntersection,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum JpipMappingAmbiguity {
    TilePartBoundary,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug, Eq, PartialEq))]
#[non_exhaustive]
pub enum DecodeError {
    MalformedInput {
        offset: u64,
        kind: MalformedKind,
    },
    UnsupportedProfile {
        feature: &'static str,
    },
    UnsupportedFeature {
        feature: &'static str,
    },
    UnsupportedComposition {
        feature: &'static str,
    },
    UnsupportedLayer {
        feature: &'static str,
    },
    UnsupportedTransform {
        feature: &'static str,
    },
    UnsupportedColorConversion {
        reason: UnsupportedColorConversion,
    },
    CodestreamIndexOutOfRange {
        index: usize,
        codestreams: usize,
    },
    LayerIndexOutOfRange {
        index: usize,
        layers: usize,
    },
    FrameIndexOutOfRange {
        index: usize,
        frames: usize,
    },
    InvalidSelection {
        reason: SelectionError,
    },
    AmbiguousJpipMapping {
        reason: JpipMappingAmbiguity,
    },
    LimitExceeded {
        resource: Resource,
        limit: u64,
        actual: u64,
    },
    /// Storage reservation was refused, including an unrepresentable capacity.
    AllocationFailed,
    Io {
        kind: IoKind,
    },
}

impl DecodeError {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures returns (Self::MalformedInput { offset, kind }),
    ))]
    pub(crate) const fn malformed(offset: u64, kind: MalformedKind) -> Self {
        Self::MalformedInput { offset, kind }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures returns (Self::LimitExceeded { resource, limit, actual }),
    ))]
    pub(crate) const fn limit(resource: Resource, limit: u64, actual: u64) -> Self {
        Self::LimitExceeded {
            resource,
            limit,
            actual,
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl fmt::Display for DecodeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedInput { offset, kind } => {
                write!(formatter, "malformed input at byte {offset}: {kind:?}")
            }
            Self::UnsupportedProfile { feature } => {
                write!(formatter, "unsupported JPEG 2000 profile: {feature}")
            }
            Self::UnsupportedFeature { feature } => {
                write!(formatter, "unsupported JPEG 2000 feature: {feature}")
            }
            Self::UnsupportedComposition { feature } => {
                write!(
                    formatter,
                    "unsupported JPX composition semantics: {feature}"
                )
            }
            Self::UnsupportedLayer { feature } => {
                write!(
                    formatter,
                    "unsupported JPX compositing-layer semantics: {feature}"
                )
            }
            Self::UnsupportedTransform { feature } => {
                write!(
                    formatter,
                    "unsupported multiple component transform: {feature}"
                )
            }
            Self::UnsupportedColorConversion { reason } => {
                write!(formatter, "unsupported color conversion: {reason:?}")
            }
            Self::CodestreamIndexOutOfRange { index, codestreams } => write!(
                formatter,
                "JPX codestream index {index} is out of range for {codestreams} codestreams"
            ),
            Self::LayerIndexOutOfRange { index, layers } => write!(
                formatter,
                "JPX compositing layer index {index} is out of range for {layers} layers"
            ),
            Self::FrameIndexOutOfRange { index, frames } => write!(
                formatter,
                "JPX composition frame index {index} is out of range for {frames} frames"
            ),
            Self::InvalidSelection { reason } => {
                write!(formatter, "invalid decode selection: {reason:?}")
            }
            Self::AmbiguousJpipMapping { reason } => {
                write!(formatter, "ambiguous JPIP precinct mapping: {reason:?}")
            }
            Self::LimitExceeded {
                resource,
                limit,
                actual,
            } => write!(
                formatter,
                "resource limit exceeded for {resource:?}: limit {limit}, actual {actual}"
            ),
            Self::AllocationFailed => write!(formatter, "memory allocation failed"),
            Self::Io { kind } => write!(formatter, "I/O failure: {kind:?}"),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl std::error::Error for DecodeError {}

#[cfg(not(verus_keep_ghost))]
impl From<std::io::Error> for DecodeError {
    fn from(error: std::io::Error) -> Self {
        let kind = match error.kind() {
            std::io::ErrorKind::NotFound => IoKind::NotFound,
            std::io::ErrorKind::PermissionDenied => IoKind::PermissionDenied,
            std::io::ErrorKind::UnexpectedEof => IoKind::UnexpectedEof,
            std::io::ErrorKind::Interrupted => IoKind::Interrupted,
            _ => IoKind::Other,
        };
        Self::Io { kind }
    }
}
