import NewLang.F1.Replace

namespace NewLang.F1
open F0
noncomputable section

def structuralStoreCandidate := installValue

/-- Discardable is the target's static type capability, including for a child.
No intermediate legal replace/result is constructed. -/
structure RawStructuralStore (canWrite typeCompatible : Prop) (s : CurrentState)
    (t : StructuralTarget) (incoming : PackageId) (v : StructuredValue)
    (fresh : NodeKey → ValueFactId) (s' : CurrentState) : Prop where
  target_live : LiveNode s.base t.location t.place
  incoming_loose : incoming ∈ s.base.loosePackages
  incoming_value : s.carried incoming = some v
  fits : FitsTarget s t v
  target_discardable : s.capability t.location t.place = true
  fresh_facts : FreshStructuralFacts s.base (affectedBy s.base t) fresh
  write_allowed : canWrite
  types_agree : typeCompatible
  post_eq : s' = structuralStoreCandidate s t incoming v fresh

def StructuralStoreStep (canWrite typeCompatible : Prop) (s : CurrentState)
    (t : StructuralTarget) (incoming : PackageId) (v : StructuredValue)
    (fresh : NodeKey → ValueFactId) (s' : CurrentState) : Prop :=
  CurrentWellFormed s ∧ RawStructuralStore canWrite typeCompatible s t incoming v fresh s' ∧
  CurrentWellFormed s'

section
variable {w ty : Prop} {s s' : CurrentState} {t : StructuralTarget}
  {incoming : PackageId} {v : StructuredValue} {fresh : NodeKey → ValueFactId}

theorem store_preserves_wellFormed
    (step : StructuralStoreStep w ty s t incoming v fresh s') : CurrentWellFormed s' := step.2.2

theorem store_post_erases_to_wellFormed_f0
    (step : StructuralStoreStep w ty s t incoming v fresh s') : F0.WellFormed (eraseToF0 s'.base) :=
  f1_wellFormed_erases_to_f0_wellFormed step.2.2.structural

theorem store_preserves_all_incarnations
    (raw : RawStructuralStore w ty s t incoming v fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).incarnation = ((s.base.root l).node p).incarnation := by rw [raw.post_eq]; rfl

theorem store_preserves_layout_and_governing_domain
    (raw : RawStructuralStore w ty s t incoming v fresh s') (l : RootLocationId) :
    (s'.base.root l).layout = (s.base.root l).layout ∧
    (s'.base.root l).governing = (s.base.root l).governing := by rw [raw.post_eq]; exact ⟨rfl,rfl⟩

theorem store_requires_target_discardable
    (raw : RawStructuralStore w ty s t incoming v fresh s') : s.capability t.location t.place = true :=
  raw.target_discardable

theorem store_rejects_nondiscardable_target (notDiscardable : s.capability t.location t.place = false) :
    ¬ RawStructuralStore w ty s t incoming v fresh s' := by
  intro raw
  have h := raw.target_discardable
  rw [notDiscardable] at h
  exact Bool.noConfusion h

theorem store_same_structural_change_set_as_replace (result : PackageId) :
    ∀ l p, (((structuralStoreCandidate s t incoming v fresh).base.root l).node p).currentFact =
      (((structuralReplaceCandidate s t incoming result v fresh).base.root l).node p).currentFact :=
  fun _ _ => rfl

theorem store_current_fact_equation
    (raw : RawStructuralStore w ty s t incoming v fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).currentFact = if (l,p) ∈ affectedBy s.base t
      then fresh (l,p) else ((s.base.root l).node p).currentFact := by rw [raw.post_eq]; rfl

theorem store_freshens_affected (raw : RawStructuralStore w ty s t incoming v fresh s')
    {l : RootLocationId} {p : PlaceId} (affected : (l,p) ∈ affectedBy s.base t) :
    ((s'.base.root l).node p).currentFact = fresh (l,p) ∧ fresh (l,p) ∉ s.base.usedValueFacts ∧
    fresh (l,p) ∈ s'.base.usedValueFacts := by
  classical
  refine ⟨?_, raw.fresh_facts.1 _ affected, ?_⟩
  · rw [store_current_fact_equation raw, ite_eq_left affected]
  · rw [raw.post_eq]; exact refresh_records_new_facts affected

theorem store_history_monotone (raw : RawStructuralStore w ty s t incoming v fresh s') :
    s.base.usedValueFacts ⊆ s'.base.usedValueFacts := by rw [raw.post_eq]; exact refresh_history_monotone _ _ _

theorem store_preserves_capability_and_incarnation_history
    (raw : RawStructuralStore w ty s t incoming v fresh s') :
    s'.capability = s.capability ∧ s'.base.usedIncarnations = s.base.usedIncarnations ∧
    s'.base.liveRoots = s.base.liveRoots ∧ s'.base.liveDomains = s.base.liveDomains ∧
    s'.base.domainValueCarrier = s.base.domainValueCarrier := by rw [raw.post_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- No result carrier is added. The input carrier is consumed; inert table data
is not a surviving value. Child old values have no independent root package ID. -/
theorem store_old_value_does_not_survive_as_result
    (raw : RawStructuralStore w ty s t incoming v fresh s') :
    s'.base.loosePackages = s.base.loosePackages.erase incoming ∧
    incoming ∉ s'.base.loosePackages ∧ s'.carried = s.carried := by
  classical
  rw [raw.post_eq]; simp [structuralStoreCandidate, installValue]

theorem store_old_root_carrier_does_not_survive (wf : CurrentWellFormed s)
    (raw : RawStructuralStore w ty s t incoming v fresh s')
    (rootTarget : t.place = (s.base.root t.location).layout.root) :
    (s.base.root t.location).package ∉ s'.base.loosePackages ∧
    ∀ l ∈ s'.base.liveRoots, (s'.base.root l).package ≠ (s.base.root t.location).package := by
  classical
  have notLoose := wf.structural.installedNotLoose t.location raw.target_live.1
  have different : incoming ≠ (s.base.root t.location).package := fun eq => notLoose (eq ▸ raw.incoming_loose)
  rw [raw.post_eq]
  constructor
  · exact fun h => notLoose (Finset.mem_of_mem_erase h)
  · intro l live same
    by_cases target : l = t.location
    · subst l; simp [structuralStoreCandidate, installValue, rootTarget] at same
      exact different same
    · have old : (s.base.root l).package = (s.base.root t.location).package := by
        simpa [structuralStoreCandidate, installValue, target, refreshCurrentFacts] using same
      exact target (wf.structural.installedUnique l live t.location raw.target_live.1 old)

theorem store_installs_new_value (raw : RawStructuralStore w ty s t incoming v fresh s')
    {q : PlaceId} (inside : q ∈ subtreePlaces (s.base.root t.location) t.place) :
    LocalDeps (s'.base.root t.location) q =
      (v.fragment (relativePosition (s.base.root t.location) t.place q)).dependencies ∧
    s'.content t.location q = (v.fragment (relativePosition (s.base.root t.location) t.place q)).content := by
  classical
  rw [raw.post_eq]; simp [structuralStoreCandidate, installValue, LocalDeps, inside]

theorem store_preserves_local_fragments_outside_target
    (raw : RawStructuralStore w ty s t incoming v fresh s') {l : RootLocationId} {q : PlaceId}
    (outside : ¬ (l = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place)) :
    LocalDeps (s'.base.root l) q = LocalDeps (s.base.root l) q ∧ s'.content l q = s.content l q := by
  classical
  rw [raw.post_eq]; simp [structuralStoreCandidate, installValue, LocalDeps, outside]

theorem store_preserves_known_disjoint_state
    (raw : RawStructuralStore w ty s t incoming v fresh s') {q : PlaceId}
    (live : LiveNode s.base t.location q)
    (disjoint : KnownDisjoint (s.base.root t.location).layout t.place q) :
    ((s'.base.root t.location).node q).currentFact = ((s.base.root t.location).node q).currentFact ∧
    LocalDeps (s'.base.root t.location) q = LocalDeps (s.base.root t.location) q ∧
    s'.content t.location q = s.content t.location q := by
  have outside : q ∉ subtreePlaces (s.base.root t.location) t.place := by
    classical
    intro h; rcases (Finset.mem_filter.mp h).2 with eq | anc
    · exact disjoint (Or.inl eq)
    · exact disjoint (Or.inr (Or.inl anc))
  refine ⟨?_, store_preserves_local_fragments_outside_target raw (by simp [outside])⟩
  rw [store_current_fact_equation raw, ite_eq_right (known_disjoint_live_node_is_not_affected live disjoint)]

theorem store_old_affected_facts_not_live (wf : CurrentWellFormed s)
    (raw : RawStructuralStore w ty s t incoming v fresh s') {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t) :
    Fact.valueFact p ((s.base.root l).node p).currentFact ∉ StructuralLiveFacts s'.base := by
  rw [raw.post_eq]; exact refreshed_old_fact_not_live wf.structural raw.fresh_facts live affected

theorem store_rejects_other_surviving_invalidated_dependency
    (wf : CurrentWellFormed s) {l m : RootLocationId} {p q : PlaceId}
    (source : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t)
    (survivor : LiveNode s.base m q)
    (outside : ¬ (m = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place))
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ LocalDeps (s.base.root m) q) :
    ¬ StructuralStoreStep w ty s t incoming v fresh s' := by
  classical
  intro step
  apply store_old_affected_facts_not_live wf step.2.1 source affected
  apply step.2.2.structural.localDependenciesValid m q
  · rw [step.2.1.post_eq]; exact survivor
  · rw [(store_preserves_local_fragments_outside_target step.2.1 outside).1]; exact dependency

theorem store_rejects_incoming_invalidated_dependency
    (wf : CurrentWellFormed s) {l : RootLocationId} {p q : PlaceId}
    (source : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t)
    (inside : q ∈ subtreePlaces (s.base.root t.location) t.place)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      (v.fragment (relativePosition (s.base.root t.location) t.place q)).dependencies) :
    ¬ StructuralStoreStep w ty s t incoming v fresh s' := by
  classical
  intro step
  apply store_old_affected_facts_not_live wf step.2.1 source affected
  apply step.2.2.structural.localDependenciesValid t.location q
  · rw [step.2.1.post_eq]; exact ⟨step.2.1.target_live.1, (Finset.mem_filter.mp inside).1⟩
  · rw [(store_installs_new_value step.2.1 inside).1]; exact dependency


theorem store_preserves_enclosing_root_carrier_for_subobject
    (raw : RawStructuralStore w ty s t incoming v fresh s')
    (subobject : t.place ≠ (s.base.root t.location).layout.root) :
    (s'.base.root t.location).package = (s.base.root t.location).package := by
  classical
  rw [raw.post_eq]; simp [structuralStoreCandidate,installValue,subobject]

theorem store_root_carrier_becomes_incoming
    (raw : RawStructuralStore w ty s t incoming v fresh s')
    (rootTarget : t.place = (s.base.root t.location).layout.root) :
    (s'.base.root t.location).package = incoming := by
  classical
  rw [raw.post_eq]; simp [structuralStoreCandidate,installValue,rootTarget]

end
end
end NewLang.F1
