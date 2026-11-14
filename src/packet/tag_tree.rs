use super::errors::{packet_reader_error, packet_reader_limit};
use super::{
    DecodeError, MalformedKind, PacketBitReader, Resource, ResourceLimits, TagTree, TagTreeLevel,
    TagTreeNode, TagTreePath, TagTreeValue,
};
#[cfg(verus_keep_ghost)]
use super::{
    packet_bit_reader_view, tag_level_view, tag_node_view, tag_path_outcome, tag_path_view,
    tag_tree_outcome, tag_tree_view,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Clone for TagTree {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tag_tree_view(&result) == tag_tree_view(self),
    ))]
    fn clone(&self) -> Self {
        Self {
            levels: self.levels.clone(),
            nodes: self.nodes.clone(),
        }
    }
}

impl TagTree {
    pub fn new(width: u32, height: u32, limits: &ResourceLimits) -> Result<Self, DecodeError> {
        tag_tree_new(width, height, limits)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == crate::specs::part1_tag_leaf_count(tag_tree_view(self)),
    ))]
    pub fn leaf_count(&self) -> Result<u64, DecodeError> {
        let level = match self.levels.first() {
            Some(level) => level,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTagTree)),
        };
        match u64::from(level.width).checked_mul(u64::from(level.height)) {
            Some(count) => Ok(count),
            None => Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == tag_tree_view(self).nodes.len(),))]
    pub const fn node_count(&self) -> usize {
        self.nodes.len()
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures tag_path_outcome(result) == crate::specs::part1_tag_path(tag_tree_view(self), leaf_x, leaf_y, error_offset),
    ))]
    fn decode_path(
        &self,
        leaf_x: u32,
        leaf_y: u32,
        error_offset: usize,
    ) -> Result<TagTreePath, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_path); }
        let leaf_level = match self.levels.first() {
            Some(level) => level,
            None => return Err(packet_reader_error(0, MalformedKind::InvalidTagTree)),
        };
        if leaf_x >= leaf_level.width || leaf_y >= leaf_level.height {
            return Err(packet_reader_error(
                error_offset,
                MalformedKind::InvalidTagTree,
            ));
        }

        let mut path = [0_usize; 64];
        let mut path_length = 0_usize;
        let mut x = leaf_x;
        let mut y = leaf_y;
        let mut level_index = 0_usize;
        #[cfg(verus_keep_ghost)]
        proof! { assert(path@ =~= Seq::new(64, |i: int| 0usize)); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost goal = crate::specs::part1_tag_path(tag_tree_view(self), leaf_x, leaf_y, error_offset);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant level_index <= self.levels.len(),
                    path_length <= 64,
                    goal == crate::specs::part1_tag_path(tag_tree_view(self), leaf_x, leaf_y, error_offset),
                    goal == crate::specs::part1_tag_path_walk(tag_tree_view(self),
                        crate::specs::Part1TagPath { nodes: path@, length: path_length }, x, y, level_index as nat, error_offset),
                decreases self.levels.len() - level_index,
            )
        )]
        while level_index < self.levels.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::specs::part1_tag_path);
                reveal(crate::specs::part1_tag_path_walk);
            }
            if path_length >= path.len() {
                return Err(packet_reader_error(
                    error_offset,
                    MalformedKind::InvalidTagTree,
                ));
            }
            let level = self.levels[level_index];
            if x >= level.width || y >= level.height {
                return Err(packet_reader_error(
                    error_offset,
                    MalformedKind::InvalidTagTree,
                ));
            }
            let physical_y = match usize::try_from(y) {
                Ok(value) => value,
                Err(_) => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            let physical_width = match usize::try_from(level.width) {
                Ok(value) => value,
                Err(_) => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            let row = match physical_y.checked_mul(physical_width) {
                Some(value) => value,
                None => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            let physical_x = match usize::try_from(x) {
                Ok(value) => value,
                Err(_) => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            let relative = match row.checked_add(physical_x) {
                Some(value) => value,
                None => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            let node_index = match level.offset.checked_add(relative) {
                Some(value) => value,
                None => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
            };
            if node_index >= self.nodes.len() {
                return Err(packet_reader_error(
                    error_offset,
                    MalformedKind::InvalidTagTree,
                ));
            }
            path[path_length] = node_index;
            path_length = path_length
                .checked_add(1)
                .ok_or_else(|| packet_reader_error(0, MalformedKind::ArithmeticOverflow))?;
            x /= 2;
            y /= 2;
            level_index = level_index
                .checked_add(1)
                .ok_or_else(|| packet_reader_error(0, MalformedKind::ArithmeticOverflow))?;
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_path_walk); }
        Ok(TagTreePath {
            nodes: path,
            length: path_length,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tag_tree_view(final(self)), packet_bit_reader_view(final(reader)))
            == crate::specs::part1_tag_reverse(tag_tree_view(old(self)), tag_path_view(path), path.length as nat,
                0, threshold, packet_bit_reader_view(old(reader))),
    ))]
    fn decode_path_nodes(
        &mut self,
        path: TagTreePath,
        threshold: u32,
        reader: &mut PacketBitReader<'_>,
    ) -> Result<TagTreeValue, DecodeError> {
        let mut inherited_low = 0_u32;
        let mut reverse_index = path.length;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost initial_tree = tag_tree_view(self);
            let ghost initial_reader = packet_bit_reader_view(reader);
            let ghost goal = crate::specs::part1_tag_reverse(initial_tree, tag_path_view(path), path.length as nat, 0, threshold, initial_reader);
        }
        #[cfg_attr(
            verus_keep_ghost,
            verus_spec(
                invariant reverse_index <= path.length,
                    initial_tree == tag_tree_view(old(self)), initial_reader == packet_bit_reader_view(old(reader)),
                    goal == crate::specs::part1_tag_reverse(initial_tree, tag_path_view(path), path.length as nat, 0, threshold, initial_reader),
                    goal == crate::specs::part1_tag_reverse(tag_tree_view(self), tag_path_view(path), reverse_index as nat,
                        inherited_low, threshold, packet_bit_reader_view(reader)),
                decreases reverse_index,
            )
        )]
        while reverse_index > 0 {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(crate::specs::part1_tag_reverse); }
            reverse_index = reverse_index
                .checked_sub(1)
                .ok_or_else(|| packet_reader_error(0, MalformedKind::ArithmeticOverflow))?;
            if reverse_index >= path.nodes.len() {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::InvalidTagTree,
                ));
            }
            let node_index = path.nodes[reverse_index];
            if node_index >= self.nodes.len() {
                return Err(packet_reader_error(
                    reader.bytes_consumed(),
                    MalformedKind::InvalidTagTree,
                ));
            }
            #[cfg(verus_keep_ghost)]
            proof_decl! { let ghost before = tag_tree_view(self); }
            let decoded = decode_tag_tree_node(
                &mut self.nodes[node_index],
                inherited_low,
                threshold,
                reader,
            );
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(tag_tree_view(self).nodes =~= before.nodes.update(node_index as int, tag_node_view(self.nodes[node_index as int])));
            }
            match decoded? {
                None => {
                    return Ok(TagTreeValue {
                        value: None,
                        is_below_threshold: false,
                    });
                }
                Some(value) => inherited_low = value,
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_reverse); }
        let leaf_index = path.nodes[0];
        if leaf_index >= self.nodes.len() {
            return Err(packet_reader_error(
                reader.bytes_consumed(),
                MalformedKind::InvalidTagTree,
            ));
        }
        let value = self.nodes[leaf_index].value;
        Ok(TagTreeValue {
            value: if value == u32::MAX { None } else { Some(value) },
            is_below_threshold: value < threshold,
        })
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures (result, tag_tree_view(final(self)), packet_bit_reader_view(final(reader)))
            == crate::specs::part1_tag_tree_decode(tag_tree_view(old(self)), leaf_x, leaf_y, threshold, packet_bit_reader_view(old(reader))),
    ))]
    pub fn decode(
        &mut self,
        leaf_x: u32,
        leaf_y: u32,
        threshold: u32,
        reader: &mut PacketBitReader<'_>,
    ) -> Result<TagTreeValue, DecodeError> {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_tree_decode); }
        let path = self.decode_path(leaf_x, leaf_y, reader.bytes_consumed())?;
        self.decode_path_nodes(path, threshold, reader)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures (result, tag_node_view(*final(node)), packet_bit_reader_view(final(reader))) ==
        crate::specs::part1_tag_node_decode(tag_node_view(*old(node)), inherited, threshold, packet_bit_reader_view(old(reader))),
))]
fn decode_tag_tree_node(
    node: &mut TagTreeNode,
    inherited: u32,
    threshold: u32,
    reader: &mut PacketBitReader<'_>,
) -> Result<Option<u32>, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost goal = crate::specs::part1_tag_node_decode(tag_node_view(*node), inherited, threshold, packet_bit_reader_view(reader)); }
    node.low = crate::refinement::tag_inherited_low(node.low, inherited);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant goal == crate::specs::part1_tag_node_decode(tag_node_view(*old(node)), inherited, threshold, packet_bit_reader_view(old(reader))),
            goal == crate::specs::part1_tag_node_loop(tag_node_view(*node), threshold, packet_bit_reader_view(reader)),
        decreases threshold as int - node.low as int, node.value as int - node.low as int,
    ))]
    while node.low < threshold && node.low < node.value {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_node_loop); }
        let bit = reader.read_bit()?;
        let next_value = crate::refinement::tag_step_value(node.low, node.value, bit);
        let next_low = if bit {
            node.low
        } else {
            crate::refinement::tag_step_low(node.low, false)
        };
        node.value = next_value;
        node.low = next_low;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(crate::specs::part1_tag_node_loop); }
    Ok(if node.value >= threshold {
        None
    } else {
        Some(node.value)
    })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_tag_storage_result(width,height,crate::limits::resource_tag_tree_node_limit(limits),tag_tree_outcome(result)),
        tag_tree_outcome(result)!=Err(DecodeError::AllocationFailed) ==> tag_tree_outcome(result) == crate::specs::part1_tag_initial(
        width, height, crate::limits::resource_tag_tree_node_limit(limits)),
))]
pub(crate) fn tag_tree_new(
    width: u32,
    height: u32,
    limits: &ResourceLimits,
) -> Result<TagTree, DecodeError> {
    tag_tree_from_dimensions(width, height, limits.maximum_tag_tree_nodes())
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures crate::specs::part1_tag_storage_result(width,height,maximum_nodes,tag_tree_outcome(result)),
        tag_tree_outcome(result)!=Err(DecodeError::AllocationFailed) ==> tag_tree_outcome(result) == crate::specs::part1_tag_initial(width, height, maximum_nodes),
))]
pub(crate) fn tag_tree_from_dimensions(
    width: u32,
    height: u32,
    maximum_nodes: u64,
) -> Result<TagTree, DecodeError> {
    #[cfg(verus_keep_ghost)]
    proof! {crate::specs::part2_tag_storage_normal(width,height,maximum_nodes);}
    if width == 0 || height == 0 {
        return Err(packet_reader_error(0, MalformedKind::InvalidTagTree));
    }
    let mut levels = Vec::new();
    let mut total_nodes = 0_usize;
    let mut level_width = width;
    let mut level_height = height;
    let mut remaining_levels = 64_usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(levels@.map_values(|level: TagTreeLevel| tag_level_view(level)) =~= Seq::<crate::specs::Part1TagLevel>::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining_levels <= 64, width != 0, height != 0,
            crate::specs::part1_tag_storage_result(width,height,maximum_nodes,crate::specs::part1_tag_initial(width,height,maximum_nodes)),
        invariant_except_break
            crate::specs::part1_tag_build(width, height, crate::specs::Part1TagBuild { levels: Seq::empty(), total: 0 }, 64, maximum_nodes)
                == crate::specs::part1_tag_build(level_width, level_height,
                    crate::specs::Part1TagBuild { levels: levels@.map_values(|level: TagTreeLevel| tag_level_view(level)), total: total_nodes },
                    remaining_levels as nat, maximum_nodes),
        ensures crate::specs::part1_tag_build(width, height, crate::specs::Part1TagBuild { levels: Seq::empty(), total: 0 }, 64, maximum_nodes)
            == Ok(crate::specs::Part1TagBuild {
                levels: levels@.map_values(|level: TagTreeLevel| tag_level_view(level)), total: total_nodes
            }),
        decreases remaining_levels,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(crate::specs::part1_tag_build); }
        if remaining_levels == 0 {
            return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow));
        }
        remaining_levels -= 1;
        let level_nodes = match u64::from(level_width).checked_mul(u64::from(level_height)) {
            Some(count) => count,
            None => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
        };
        let next_total = match (total_nodes as u64).checked_add(level_nodes) {
            Some(count) => count,
            None => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
        };
        if next_total > maximum_nodes {
            return Err(packet_reader_limit(
                Resource::TagTreeNodes,
                maximum_nodes,
                next_total,
            ));
        }
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous_levels = levels@.map_values(|level: TagTreeLevel| tag_level_view(level)); }
        levels.push(TagTreeLevel {
            offset: total_nodes,
            width: level_width,
            height: level_height,
        });
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(levels@.map_values(|level: TagTreeLevel| tag_level_view(level)) =~= previous_levels.push(
                crate::specs::Part1TagLevel { offset: total_nodes, width: level_width, height: level_height }));
        }
        total_nodes = match usize::try_from(next_total) {
            Ok(total) => total,
            Err(_) => return Err(packet_reader_error(0, MalformedKind::ArithmeticOverflow)),
        };
        if level_width == 1 && level_height == 1 {
            break;
        }
        level_width = ceil_div_two(level_width);
        level_height = ceil_div_two(level_height);
    }
    let filled = crate::allocation::filled_values(
        TagTreeNode {
            low: 0,
            value: u32::MAX,
        },
        total_nodes,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::specs::part2_tag_storage_observed(width,height,maximum_nodes,
            crate::specs::Part1TagBuild {levels:levels@.map_values(|level:TagTreeLevel|tag_level_view(level)),total:total_nodes},
            match filled {Ok(_)=>Ok(()),Err(error)=>Err(error)});
    }
    let nodes = filled?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(nodes@.map_values(|node: TagTreeNode| tag_node_view(node)) =~=
            Seq::new(total_nodes as nat, |i: int| crate::specs::Part1TagNode { low: 0, value: u32::MAX }));
    }
    Ok(TagTree { levels, nodes })
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (value as nat / 2 + value as nat % 2) as u32,
))]
const fn ceil_div_two(value: u32) -> u32 {
    value / 2 + value % 2
}
