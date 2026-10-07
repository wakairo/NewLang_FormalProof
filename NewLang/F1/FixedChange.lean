import NewLang.F1.Replace
import NewLang.F0.Reference

/-! Bounded fixed-subobject integration over the reviewed F1.1 definitions.
No new operation, pointer representation, or abstract effect system is introduced. -/
namespace NewLang.F1.FixedChange
open F0
noncomputable section

section Replace
variable {w ty : Prop} {s post : CurrentState} {t : StructuralTarget}
  {incoming result : PackageId} {v : StructuredValue} {fresh : NodeKey → ValueFactId}

/-- Fixed lifetime identity and the enclosing carrier are independent of changed values. -/
theorem field_replace_preserves_target_and_root_identity
    (raw : RawStructuralReplace w ty s t incoming result v fresh post)
    (field : t.place ≠ (s.base.root t.location).layout.root) :
    (post.base.root t.location).layout = (s.base.root t.location).layout ∧
    ((post.base.root t.location).node t.place).incarnation =
      ((s.base.root t.location).node t.place).incarnation ∧
    ((post.base.root t.location).node (s.base.root t.location).layout.root).incarnation =
      ((s.base.root t.location).node (s.base.root t.location).layout.root).incarnation ∧
    (post.base.root t.location).governing = (s.base.root t.location).governing ∧
    (post.base.root t.location).package = (s.base.root t.location).package :=
  ⟨replace_preserves_layout raw _, replace_preserves_all_incarnations raw _ _,
    replace_preserves_all_incarnations raw _ _, replace_preserves_governing_domain raw _,
    replace_preserves_enclosing_root_carrier_for_subobject raw field⟩

/-- This is incarnation liveness, not a missing field-ptr acquisition theorem. -/
theorem field_replace_preserves_target_incarnation_liveness
    (raw : RawStructuralReplace w ty s t incoming result v fresh post) :
    LiveNode post.base t.location t.place ∧
    StructuralLiveIncarnation post.base ((s.base.root t.location).node t.place).incarnation := by
  have live : LiveNode post.base t.location t.place := by
    rw [raw.post_eq]; exact raw.target_live
  exact ⟨live, t.location, t.place, live, replace_preserves_all_incarnations raw _ _⟩

theorem field_replace_frames_known_disjoint_value
    (raw : RawStructuralReplace w ty s t incoming result v fresh post) {q : PlaceId}
    (live : LiveNode s.base t.location q)
    (disjoint : KnownDisjoint (s.base.root t.location).layout t.place q) :
    ((post.base.root t.location).node q).currentFact =
      ((s.base.root t.location).node q).currentFact ∧
    post.content t.location q = s.content t.location q ∧
    LocalDeps (post.base.root t.location) q = LocalDeps (s.base.root t.location) q ∧
    Fact.valueFact q ((s.base.root t.location).node q).currentFact ∈
      StructuralLiveFacts post.base := by
  classical
  have outside : ¬ (t.location = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place) := by
    rintro ⟨_, inside⟩
    rcases (Finset.mem_filter.mp inside).2 with same | below
    · exact disjoint (Or.inl same)
    · exact disjoint (Or.inr (Or.inl below))
  have frame := replace_preserves_local_fragments_outside_target raw outside
  exact ⟨replace_preserves_known_disjoint_current_facts raw live disjoint,
    frame.2, frame.1, replace_preserves_disjoint_live_facts raw live disjoint⟩

/-- Ancestors refresh even though their local fragment can be preserved. -/
theorem field_replace_refreshes_ancestor_and_ends_old_fact
    (wf : CurrentWellFormed s)
    (raw : RawStructuralReplace w ty s t incoming result v fresh post) {p : PlaceId}
    (live : LiveNode s.base t.location p)
    (ancestor : Ancestor (s.base.root t.location).layout p t.place) :
    ((post.base.root t.location).node p).currentFact = fresh (t.location,p) ∧
    fresh (t.location,p) ∉ s.base.usedValueFacts ∧
    fresh (t.location,p) ∈ post.base.usedValueFacts ∧
    Fact.valueFact p ((s.base.root t.location).node p).currentFact ∉
      StructuralLiveFacts post.base ∧
    ((s.base.root t.location).node p).currentFact ∈ post.base.usedValueFacts := by
  have affected := ancestor_of_target_is_affected live ancestor
  have newFact := replace_freshens_affected raw affected
  exact ⟨newFact.1, newFact.2.1, newFact.2.2,
    replace_old_affected_facts_not_live wf raw live affected,
    replace_history_monotone raw (wf.structural.valueFactsRecorded _ _ live)⟩

/-- A target's own dependent value survives as the returned old value in replace. -/
theorem field_replace_rejects_returned_target_dependency
    (wf : CurrentWellFormed s) (live : LiveNode s.base t.location t.place)
    (dependency : Fact.valueFact t.place ((s.base.root t.location).node t.place).currentFact ∈
      LocalDeps (s.base.root t.location) t.place) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh post := by
  apply replace_rejects_old_result_invalidated_dependency wf live (target_is_affected live)
  rw [extract_value_dependencies wf live.1]
  exact local_deps_subset_subtree_deps live.2 dependency

/-- Overlap includes target, ancestor and descendant facts; ownership must survive. -/
theorem field_replace_rejects_surviving_overlapping_dependency
    (wf : CurrentWellFormed s) {p q : PlaceId} {m : RootLocationId}
    (source : LiveNode s.base t.location p)
    (overlap : StructuralOverlap (s.base.root t.location).layout t.place p)
    (owner : LiveNode s.base m q)
    (outside : ¬ (m = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place))
    (dependency : Fact.valueFact p ((s.base.root t.location).node p).currentFact ∈
      LocalDeps (s.base.root m) q) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh post :=
  replace_rejects_other_surviving_invalidated_dependency wf source
    (mem_affectedBy.mpr ⟨source, rfl, overlap⟩) owner outside dependency

/-- Keeping a larger finite may-set cannot drop an included overlapping blocker.
This is not a soundness theorem for an unimplemented Unknown-effect analysis. -/
theorem field_replace_dependency_superset_keeps_blocker
    (wf : CurrentWellFormed s) {p q : PlaceId} {m : RootLocationId}
    (source : LiveNode s.base t.location p)
    (overlap : StructuralOverlap (s.base.root t.location).layout t.place p)
    (owner : LiveNode s.base m q)
    (outside : ¬ (m = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place))
    (possible : Finset Fact) (retained : possible ⊆ LocalDeps (s.base.root m) q)
    (blocker : Fact.valueFact p ((s.base.root t.location).node p).currentFact ∈ possible) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh post :=
  field_replace_rejects_surviving_overlapping_dependency wf source overlap owner outside (retained blocker)

/-- Root-only point acquisition after rich field Change, through sound state erasure.
This makes no coarse-to-rich legality inference and says nothing about a field ptr. -/
theorem field_replace_allows_enclosing_root_ptr_acquisition
    (step : StructuralReplaceStep w ty s t incoming result v fresh post)
    {stable access : Prop} (evidence : stable) (allowed : access) :
    AcquireRef stable access (eraseToF0 post.base)
      ⟨t.location, ((s.base.root t.location).node (s.base.root t.location).layout.root).incarnation⟩
      (s.base.root t.location).governing := by
  refine ⟨replace_post_erases_to_wellFormed_f0 step, ⟨⟨eraseRoot (post.base.root t.location), ?_, ?_, ?_⟩,
    evidence, allowed⟩⟩
  · apply (erase_occupancy_live_iff _ _ _).mpr
    exact ⟨(replace_preserves_fixed_support_and_incarnation_history step.2.1).1.symm ▸ step.2.1.target_live.1, rfl⟩
  · change ((post.base.root t.location).node (post.base.root t.location).layout.root).incarnation = _
    rw [replace_preserves_layout step.2.1]
    exact replace_preserves_all_incarnations step.2.1 _ _
  · exact replace_preserves_governing_domain step.2.1 _

end Replace

/-- The root-only erased pointer interface cannot stand in for a field pointer.
This is a missing modeling hook, not a normative prohibition on field ptrs. -/
theorem erased_field_incarnation_cannot_acquire_as_root
    {s : CurrentState} (wf : CurrentWellFormed s) {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s.base l p) (field : p ≠ (s.base.root l).layout.root)
    (stable access : Prop) (d : DomainId) :
    ¬ AcquireRef stable access (eraseToF0 s.base)
      ⟨l, ((s.base.root l).node p).incarnation⟩ d := by
  apply acquire_ref_rejects_incarnation_mismatch (root := eraseRoot (s.base.root l))
    ((erase_occupancy_live_iff _ _ _).mpr ⟨live.1, rfl⟩)
  apply distinct_live_nodes_have_distinct_incarnations wf.structural live
    ⟨live.1, (wf.structural.trees l live.1).root_tracked⟩
  intro same
  exact field (congrArg Prod.snd same)

end
end NewLang.F1.FixedChange
