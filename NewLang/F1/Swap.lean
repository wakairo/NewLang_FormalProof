import NewLang.F1.Store

namespace NewLang.F1
open F0
noncomputable section

def StructuralTargetsDisjoint (s : State) (a b : StructuralTarget) : Prop :=
  a.location ≠ b.location ∨
    (a.location = b.location ∧ KnownDisjoint (s.root a.location).layout a.place b.place)

def swapAffected (s : State) (a b : StructuralTarget) : Finset NodeKey := affectedBy s a ∪ affectedBy s b

/-- One simultaneous exchange, using pre-state extractions on both sides. A shared
ancestor occurs once in the finite union and receives exactly one new fact. -/
def structuralSwapCandidate (s : CurrentState) (a b : StructuralTarget)
    (fresh : NodeKey → ValueFactId) : CurrentState := by
  classical
  let av := extractValue s a
  let bv := extractValue s b
  let refreshed := refreshCurrentFacts s.base (swapAffected s.base a b) fresh
  let incoming := fun l p =>
    if l = a.location ∧ p ∈ subtreePlaces (s.base.root a.location) a.place then
      some (bv.fragment (relativePosition (s.base.root a.location) a.place p))
    else if l = b.location ∧ p ∈ subtreePlaces (s.base.root b.location) b.place then
      some (av.fragment (relativePosition (s.base.root b.location) b.place p)) else none
  exact { s with
    base := { refreshed with root := fun l => { refreshed.root l with
      node := fun p => { (refreshed.root l).node p with localDeps :=
        ((incoming l p).map (fun f => f.dependencies)).getD (LocalDeps (s.base.root l) p) }
      package := if a.place = (s.base.root a.location).layout.root ∧ b.place = (s.base.root b.location).layout.root
        then if l = a.location then (s.base.root b.location).package
          else if l = b.location then (s.base.root a.location).package else (s.base.root l).package
        else (s.base.root l).package } }
    content := fun l p => ((incoming l p).map (fun f => f.content)).getD (s.content l p) }

structure RawStructuralSwapDistinct (canWrite typeCompatible : Prop) (s : CurrentState)
    (a b : StructuralTarget) (fresh : NodeKey → ValueFactId) (s' : CurrentState) : Prop where
  left_live : LiveNode s.base a.location a.place
  right_live : LiveNode s.base b.location b.place
  disjoint : StructuralTargetsDisjoint s.base a b
  left_fits : FitsTarget s a (extractValue s b)
  right_fits : FitsTarget s b (extractValue s a)
  fresh_facts : FreshStructuralFacts s.base (swapAffected s.base a b) fresh
  write_allowed : canWrite
  types_agree : typeCompatible
  post_eq : s' = structuralSwapCandidate s a b fresh

/-- Same-place carries no fresh supply. Distinct-place carries its checked supply. -/
inductive RawStructuralSwap (canWrite typeCompatible : Prop) :
    CurrentState → StructuralTarget → StructuralTarget → CurrentState → Prop where
  | same {s : CurrentState} {a : StructuralTarget} :
      LiveNode s.base a.location a.place → canWrite → typeCompatible → RawStructuralSwap canWrite typeCompatible s a a s
  | distinct {s s' : CurrentState} {a b : StructuralTarget} {fresh : NodeKey → ValueFactId} :
      RawStructuralSwapDistinct canWrite typeCompatible s a b fresh s' → RawStructuralSwap canWrite typeCompatible s a b s'

def StructuralSwapStep (canWrite typeCompatible : Prop) (s : CurrentState)
    (a b : StructuralTarget) (s' : CurrentState) : Prop :=
  CurrentWellFormed s ∧ RawStructuralSwap canWrite typeCompatible s a b s' ∧ CurrentWellFormed s'

section
variable {w ty : Prop} {s s' : CurrentState} {a b : StructuralTarget} {fresh : NodeKey → ValueFactId}

theorem disjoint_targets_are_distinct (disjoint : StructuralTargetsDisjoint s.base a b) : a ≠ b := by
  intro same; subst b
  rcases disjoint with different | ⟨_, noOverlap⟩
  · exact different rfl
  · exact noOverlap (Or.inl rfl)

theorem swap_same_is_identity (raw : RawStructuralSwap w ty s a a s') : s' = s := by
  cases raw with
  | same => rfl
  | distinct raw => exact False.elim (disjoint_targets_are_distinct raw.disjoint rfl)

theorem swap_same_consumes_no_fresh_fact (raw : RawStructuralSwap w ty s a a s') :
    s'.base.usedValueFacts = s.base.usedValueFacts ∧ s'.base.usedIncarnations = s.base.usedIncarnations := by
  rw [swap_same_is_identity raw]; exact ⟨rfl,rfl⟩

theorem swap_preserves_wellFormed (step : StructuralSwapStep w ty s a b s') : CurrentWellFormed s' := step.2.2

theorem swap_post_erases_to_wellFormed_f0 (step : StructuralSwapStep w ty s a b s') :
    F0.WellFormed (eraseToF0 s'.base) := f1_wellFormed_erases_to_f0_wellFormed step.2.2.structural

theorem swap_distinct_requires_disjoint_targets
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') : StructuralTargetsDisjoint s.base a b := raw.disjoint

theorem swap_distinct_preserves_all_incarnations
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).incarnation = ((s.base.root l).node p).incarnation := by rw [raw.post_eq]; rfl

theorem swap_distinct_preserves_layout_and_governing_domains
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') (l : RootLocationId) :
    (s'.base.root l).layout = (s.base.root l).layout ∧
    (s'.base.root l).governing = (s.base.root l).governing := by rw [raw.post_eq]; exact ⟨rfl,rfl⟩

theorem swap_distinct_preserves_carriers_and_domains
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') :
    s'.base.loosePackages = s.base.loosePackages ∧ s'.base.looseValues = s.base.looseValues ∧
    s'.carried = s.carried ∧ s'.base.liveDomains = s.base.liveDomains ∧
    s'.base.domainValueCarrier = s.base.domainValueCarrier ∧ s'.base.usedIncarnations = s.base.usedIncarnations ∧
    s'.capability = s.capability ∧ s'.base.liveRoots = s.base.liveRoots := by
  rw [raw.post_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem swap_distinct_current_fact_equation
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).currentFact = if (l,p) ∈ swapAffected s.base a b
      then fresh (l,p) else ((s.base.root l).node p).currentFact := by rw [raw.post_eq]; rfl

theorem swap_distinct_creates_fresh_current_facts
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {l : RootLocationId} {p : PlaceId}
    (affected : (l,p) ∈ swapAffected s.base a b) :
    ((s'.base.root l).node p).currentFact = fresh (l,p) ∧ fresh (l,p) ∉ s.base.usedValueFacts ∧
    fresh (l,p) ∈ s'.base.usedValueFacts := by
  classical
  refine ⟨?_, raw.fresh_facts.1 _ affected, ?_⟩
  · rw [swap_distinct_current_fact_equation raw, ite_eq_left affected]
  · rw [raw.post_eq]; exact refresh_records_new_facts affected

theorem swap_distinct_history_monotone (raw : RawStructuralSwapDistinct w ty s a b fresh s') :
    s.base.usedValueFacts ⊆ s'.base.usedValueFacts := by rw [raw.post_eq]; exact refresh_history_monotone _ _ _

theorem swap_distinct_new_fact_ids_are_pairwise_distinct
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {q r : NodeKey}
    (qChanged : q ∈ swapAffected s.base a b) (rChanged : r ∈ swapAffected s.base a b) (different : q ≠ r) :
    fresh q ≠ fresh r := fresh_structural_facts_reject_aliasing raw.fresh_facts qChanged rChanged different

theorem swap_distinct_preserves_unaffected_current_facts
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {l : RootLocationId} {p : PlaceId}
    (_live : LiveNode s.base l p) (unaffected : (l,p) ∉ swapAffected s.base a b) :
    ((s'.base.root l).node p).currentFact = ((s.base.root l).node p).currentFact := by
  rw [swap_distinct_current_fact_equation raw, ite_eq_right unaffected]

theorem swap_distinct_old_affected_facts_not_live (wf : CurrentWellFormed s)
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s.base l p) (affected : (l,p) ∈ swapAffected s.base a b) :
    Fact.valueFact p ((s.base.root l).node p).currentFact ∉ StructuralLiveFacts s'.base := by
  rw [raw.post_eq]; exact refreshed_old_fact_not_live wf.structural raw.fresh_facts live affected

theorem swap_distinct_installs_right_value_at_left
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root a.location) a.place) :
    LocalDeps (s'.base.root a.location) q =
      ((extractValue s b).fragment (relativePosition (s.base.root a.location) a.place q)).dependencies ∧
    s'.content a.location q =
      ((extractValue s b).fragment (relativePosition (s.base.root a.location) a.place q)).content := by
  classical
  rw [raw.post_eq]; simp [structuralSwapCandidate, inside, LocalDeps]

/-- Disjointness forbids a node from belonging to both target subtrees. -/
theorem disjoint_subtrees_have_no_common_node {layout : StructuralLayout} (tree : TreeWellFormed layout)
    {p q r : PlaceId} (disjoint : KnownDisjoint layout p q)
    (left : Below layout p r) (right : Below layout q r) : False := by
  rcases left with rfl | left
  · rcases right with eq | ancestor
    · exact disjoint (Or.inl eq.symm)
    · exact disjoint (Or.inr (Or.inr ancestor))
  rcases right with rfl | right
  · exact disjoint (Or.inr (Or.inl left))
  rcases left with ⟨pt, _, ps, _, pe⟩
  rcases right with ⟨qt, _, qs, _, qe⟩
  have prefixP : layout.path p <+: layout.path r := ⟨ps, pe.symm⟩
  have prefixQ : layout.path q <+: layout.path r := ⟨qs, qe.symm⟩
  rcases List.prefix_or_prefix_of_prefix prefixP prefixQ with pq | qp
  · rcases pq with ⟨suffix, eq⟩
    by_cases empty : suffix = []
    · subst suffix
      have same := tree.paths_unique p pt q qt (by simpa using eq)
      exact disjoint (Or.inl same)
    · exact disjoint (Or.inr (Or.inl ⟨pt, qt, suffix, empty, eq.symm⟩))
  · rcases qp with ⟨suffix, eq⟩
    by_cases empty : suffix = []
    · subst suffix
      have same := tree.paths_unique q qt p pt (by simpa using eq)
      exact disjoint (Or.inl same.symm)
    · exact disjoint (Or.inr (Or.inr ⟨qt, pt, suffix, empty, eq.symm⟩))


theorem swap_right_subtree_is_outside_left (wf : CurrentWellFormed s)
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root b.location) b.place) :
    ¬ (b.location = a.location ∧ q ∈ subtreePlaces (s.base.root a.location) a.place) := by
  classical
  rintro ⟨same, other⟩
  rcases raw.disjoint with different | ⟨_, disjoint⟩
  · exact different same.symm
  · apply disjoint_subtrees_have_no_common_node (wf.structural.trees _ raw.left_live.1) disjoint
      (Finset.mem_filter.mp other).2
    simpa [same] using (Finset.mem_filter.mp inside).2

theorem swap_distinct_installs_left_value_at_right (wf : CurrentWellFormed s)
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root b.location) b.place) :
    LocalDeps (s'.base.root b.location) q =
      ((extractValue s a).fragment (relativePosition (s.base.root b.location) b.place q)).dependencies ∧
    s'.content b.location q =
      ((extractValue s a).fragment (relativePosition (s.base.root b.location) b.place q)).content := by
  classical
  have outside := swap_right_subtree_is_outside_left wf raw inside
  rw [raw.post_eq]; simp [structuralSwapCandidate, inside, outside, LocalDeps]

theorem swap_distinct_exchanges_complete_structured_values (wf : CurrentWellFormed s)
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') :
    (∀ q ∈ subtreePlaces (s.base.root a.location) a.place,
      LocalDeps (s'.base.root a.location) q =
        ((extractValue s b).fragment (relativePosition (s.base.root a.location) a.place q)).dependencies ∧
      s'.content a.location q =
        ((extractValue s b).fragment (relativePosition (s.base.root a.location) a.place q)).content ∧
      s'.capability a.location q =
        (extractValue s b).discardable (relativePosition (s.base.root a.location) a.place q)) ∧
    (∀ q ∈ subtreePlaces (s.base.root b.location) b.place,
      LocalDeps (s'.base.root b.location) q =
        ((extractValue s a).fragment (relativePosition (s.base.root b.location) b.place q)).dependencies ∧
      s'.content b.location q =
        ((extractValue s a).fragment (relativePosition (s.base.root b.location) b.place q)).content ∧
      s'.capability b.location q =
        (extractValue s a).discardable (relativePosition (s.base.root b.location) b.place q)) := by
  constructor
  · intro q inside
    have installed := swap_distinct_installs_right_value_at_left raw inside
    refine ⟨installed.1, installed.2, ?_⟩
    rw [raw.post_eq]; exact (raw.left_fits.2 q inside).symm
  · intro q inside
    have installed := swap_distinct_installs_left_value_at_right wf raw inside
    refine ⟨installed.1, installed.2, ?_⟩
    rw [raw.post_eq]; exact (raw.right_fits.2 q inside).symm

theorem swap_preserves_external_disjoint_state
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {l : RootLocationId} {q : PlaceId}
    (live : LiveNode s.base l q) (unaffected : (l,q) ∉ swapAffected s.base a b)
    (outsideA : ¬ (l = a.location ∧ q ∈ subtreePlaces (s.base.root a.location) a.place))
    (outsideB : ¬ (l = b.location ∧ q ∈ subtreePlaces (s.base.root b.location) b.place)) :
    ((s'.base.root l).node q).currentFact = ((s.base.root l).node q).currentFact ∧
    LocalDeps (s'.base.root l) q = LocalDeps (s.base.root l) q ∧
    s'.content l q = s.content l q ∧
    Fact.valueFact q ((s.base.root l).node q).currentFact ∈ StructuralLiveFacts s'.base := by
  have fact := swap_distinct_preserves_unaffected_current_facts raw live unaffected
  refine ⟨fact, ?_, ?_, l, ?_, ?_, fact⟩
  · rw [raw.post_eq]; simp [structuralSwapCandidate, outsideA, outsideB, LocalDeps]
  · rw [raw.post_eq]; simp [structuralSwapCandidate, outsideA, outsideB]
  · rw [raw.post_eq]; exact live.1
  · rw [(swap_distinct_preserves_layout_and_governing_domains raw l).1]; exact live.2

/-- Rejection comes solely from the candidate's surviving local dependency. -/
theorem swap_rejects_right_value_old_fact_dependency (wf : CurrentWellFormed s)
    {l : RootLocationId} {p q : PlaceId} (source : LiveNode s.base l p)
    (affected : (l,p) ∈ swapAffected s.base a b)
    (inside : q ∈ subtreePlaces (s.base.root a.location) a.place)
    (dep : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      ((extractValue s b).fragment (relativePosition (s.base.root a.location) a.place q)).dependencies) :
    ¬ (RawStructuralSwapDistinct w ty s a b fresh s' ∧ CurrentWellFormed s') := by
  classical
  rintro ⟨raw, post⟩
  apply swap_distinct_old_affected_facts_not_live wf raw source affected
  apply post.structural.localDependenciesValid a.location q
  · rw [raw.post_eq]; exact ⟨raw.left_live.1, (Finset.mem_filter.mp inside).1⟩
  · rw [(swap_distinct_installs_right_value_at_left raw inside).1]; exact dep

theorem swap_rejects_left_value_old_fact_dependency (wf : CurrentWellFormed s)
    {l : RootLocationId} {p q : PlaceId} (source : LiveNode s.base l p)
    (affected : (l,p) ∈ swapAffected s.base a b)
    (inside : q ∈ subtreePlaces (s.base.root b.location) b.place)
    (dep : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      ((extractValue s a).fragment (relativePosition (s.base.root b.location) b.place q)).dependencies) :
    ¬ (RawStructuralSwapDistinct w ty s a b fresh s' ∧ CurrentWellFormed s') := by
  classical
  rintro ⟨raw, post⟩
  apply swap_distinct_old_affected_facts_not_live wf raw source affected
  apply post.structural.localDependenciesValid b.location q
  · rw [raw.post_eq]; exact ⟨raw.right_live.1, (Finset.mem_filter.mp inside).1⟩
  · rw [(swap_distinct_installs_left_value_at_right wf raw inside).1]; exact dep


theorem swap_preserves_local_fragments_outside_targets
    (raw : RawStructuralSwapDistinct w ty s a b fresh s') {l : RootLocationId} {q : PlaceId}
    (outsideA : ¬ (l = a.location ∧ q ∈ subtreePlaces (s.base.root a.location) a.place))
    (outsideB : ¬ (l = b.location ∧ q ∈ subtreePlaces (s.base.root b.location) b.place)) :
    LocalDeps (s'.base.root l) q = LocalDeps (s.base.root l) q ∧ s'.content l q = s.content l q := by
  classical
  rw [raw.post_eq]; simp [structuralSwapCandidate, LocalDeps, outsideA, outsideB]


theorem swap_rejects_external_surviving_invalidated_dependency (wf : CurrentWellFormed s)
    {l m : RootLocationId} {p q : PlaceId} (source : LiveNode s.base l p)
    (affected : (l,p) ∈ swapAffected s.base a b) (survivor : LiveNode s.base m q)
    (outsideA : ¬ (m = a.location ∧ q ∈ subtreePlaces (s.base.root a.location) a.place))
    (outsideB : ¬ (m = b.location ∧ q ∈ subtreePlaces (s.base.root b.location) b.place))
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ LocalDeps (s.base.root m) q) :
    ¬ (RawStructuralSwapDistinct w ty s a b fresh s' ∧ CurrentWellFormed s') := by
  rintro ⟨raw,post⟩
  apply swap_distinct_old_affected_facts_not_live wf raw source affected
  apply post.structural.localDependenciesValid m q
  · rw [raw.post_eq]; exact survivor
  · rw [(swap_preserves_local_fragments_outside_targets raw outsideA outsideB).1]; exact dependency

theorem swap_whole_root_carriers_are_exchanged
    (raw : RawStructuralSwapDistinct w ty s a b fresh s')
    (leftRoot : a.place = (s.base.root a.location).layout.root)
    (rightRoot : b.place = (s.base.root b.location).layout.root) :
    (s'.base.root a.location).package = (s.base.root b.location).package ∧
    (s'.base.root b.location).package = (s.base.root a.location).package := by
  classical
  have locationsDifferent : a.location ≠ b.location := by
    intro same
    rcases raw.disjoint with different|⟨_,disjoint⟩
    · exact different same
    · have placesSame : a.place = b.place := leftRoot.trans (by rw [same]; exact rightRoot.symm)
      exact disjoint (Or.inl placesSame)
  rw [raw.post_eq]
  simp [structuralSwapCandidate,leftRoot,rightRoot,locationsDifferent,locationsDifferent.symm]

end
end
end NewLang.F1
