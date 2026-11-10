#[cfg(verus_keep_ghost)]
verus! {
    pub closed spec fn jpip_transition_view(value: &JpipTilePartTransition) -> crate::specs::Part2JpipTransition {
        (value.tile, value.tile_part, value.packet_count, value.data_length, value.functional, value.header@)
    }

    pub open spec fn jpip_transitions_view(value: &Vec<JpipTilePartTransition>) -> Seq<crate::specs::Part2JpipTransition> {
        value@.map_values(|transition: JpipTilePartTransition| jpip_transition_view(&transition))
    }

    pub open spec fn jpip_transitions_outcome(value: Result<Vec<JpipTilePartTransition>, DecodeError>)
        -> Result<Seq<crate::specs::Part2JpipTransition>, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_transitions_view(&value)) }
    }

    pub closed spec fn jpip_semantic_need_view(value: JpipSemanticNeed) -> crate::specs::Part2JpipSemanticNeed {
        (value.kind, value.identifier)
    }

    pub open spec fn jpip_semantic_needs_view(value: &Vec<JpipSemanticNeed>) -> Seq<crate::specs::Part2JpipSemanticNeed> {
        value@.map_values(|need: JpipSemanticNeed| jpip_semantic_need_view(need))
    }

    pub closed spec fn jpip_transition_report_view(value: &JpipTilePartTransitionReport)
        -> crate::specs::Part2JpipTransitionReport {
        (value.status, jpip_transitions_view(&value.transitions),
            jpip_semantic_needs_view(&value.needs), jpip_missing_views(&value.missing))
    }

    pub open spec fn jpip_transition_report_outcome(value: Result<JpipTilePartTransitionReport, DecodeError>)
        -> Result<crate::specs::Part2JpipTransitionReport, DecodeError> {
        match value { Err(error) => Err(error), Ok(value) => Ok(jpip_transition_report_view(&value)) }
    }

    proof fn jpip_transition_sequence_shapes()
        ensures
            forall|values: &Vec<JpipTilePartTransition>| values@.len() == 0 ==>
                #[trigger] jpip_transitions_view(values) == Seq::empty(),
            forall|values: &Vec<JpipTilePartTransition>| values@.len() == 1 ==>
                #[trigger] jpip_transitions_view(values) == seq![jpip_transition_view(&values@[0])],
            forall|values: &Vec<JpipSemanticNeed>| values@.len() == 0 ==>
                #[trigger] jpip_semantic_needs_view(values) == Seq::empty(),
            forall|values: &Vec<JpipSemanticNeed>| values@.len() == 1 ==>
                #[trigger] jpip_semantic_needs_view(values) == seq![jpip_semantic_need_view(values@[0])],
            forall|values: &Vec<JpipMissingRange>| values@.len() == 0 ==>
                #[trigger] jpip_missing_views(values) == Seq::empty(),
    {
        assert forall|values: &Vec<JpipTilePartTransition>| values@.len() == 0 ==>
            #[trigger] jpip_transitions_view(values) == Seq::empty() by {
            if values@.len() == 0 { assert(jpip_transitions_view(values) =~= Seq::empty()); }
        }
        assert forall|values: &Vec<JpipTilePartTransition>| values@.len() == 1 ==>
            #[trigger] jpip_transitions_view(values) == seq![jpip_transition_view(&values@[0])] by {
            if values@.len() == 1 { assert(jpip_transitions_view(values) =~= seq![jpip_transition_view(&values@[0])]); }
        }
        assert forall|values: &Vec<JpipSemanticNeed>| values@.len() == 0 ==>
            #[trigger] jpip_semantic_needs_view(values) == Seq::empty() by {
            if values@.len() == 0 { assert(jpip_semantic_needs_view(values) =~= Seq::empty()); }
        }
        assert forall|values: &Vec<JpipSemanticNeed>| values@.len() == 1 ==>
            #[trigger] jpip_semantic_needs_view(values) == seq![jpip_semantic_need_view(values@[0])] by {
            if values@.len() == 1 { assert(jpip_semantic_needs_view(values) =~= seq![jpip_semantic_need_view(values@[0])]); }
        }
        assert forall|values: &Vec<JpipMissingRange>| values@.len() == 0 ==>
            #[trigger] jpip_missing_views(values) == Seq::empty() by {
            if values@.len() == 0 { assert(jpip_missing_views(values) =~= Seq::empty()); }
        }
    }
}
