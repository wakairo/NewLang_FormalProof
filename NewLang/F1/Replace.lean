import NewLang.F1.CurrentFacts

namespace NewLang.F1
open F0
noncomputable section

/-- Install only the target subtree's semantic fragments. Ancestor LocalDeps remain.
Root carrier identity changes only for a whole-root target. -/
def installValue (s : CurrentState) (t : StructuralTarget) (incoming : PackageId)
    (v : StructuredValue) (fresh : NodeKey → ValueFactId) : CurrentState := by
  classical
  let refreshed := refreshCurrentFacts s.base (affectedBy s.base t) fresh
  exact { s with
    base := { refreshed with
      root := fun l => { refreshed.root l with
        node := fun p => { (refreshed.root l).node p with localDeps :=
          (if l = t.location ∧ p ∈ subtreePlaces (s.base.root t.location) t.place
          then (v.fragment (relativePosition (s.base.root t.location) t.place p)).dependencies
          else LocalDeps (s.base.root l) p) }
        package := if l = t.location ∧ t.place = (s.base.root l).layout.root
          then incoming else (s.base.root l).package }
      loosePackages := s.base.loosePackages.erase incoming }
    content := fun l p => if l = t.location ∧ p ∈ subtreePlaces (s.base.root t.location) t.place
      then (v.fragment (relativePosition (s.base.root t.location) t.place p)).content else s.content l p }

def structuralReplaceCandidate (s : CurrentState) (t : StructuralTarget)
    (incoming result : PackageId) (v : StructuredValue) (fresh : NodeKey → ValueFactId) : CurrentState := by
  classical
  let installed := installValue s t incoming v fresh
  let old := extractValue s t
  exact { installed with
    base := { installed.base with
      loosePackages := insert result installed.base.loosePackages
      looseValues := fun pkg => if pkg = result then some old.summary else s.base.looseValues pkg }
    carried := fun pkg => if pkg = result then some old else s.carried pkg }

/-- Static/caller obligations are propositions, not fabricated authorization capabilities. -/
structure RawStructuralReplace (canWrite typeCompatible : Prop) (s : CurrentState)
    (t : StructuralTarget) (incoming result : PackageId) (v : StructuredValue)
    (fresh : NodeKey → ValueFactId) (s' : CurrentState) : Prop where
  target_live : LiveNode s.base t.location t.place
  incoming_loose : incoming ∈ s.base.loosePackages
  incoming_value : s.carried incoming = some v
  fits : FitsTarget s t v
  result_identity : if t.place = (s.base.root t.location).layout.root
    then result = (s.base.root t.location).package
    else result ∉ s.base.loosePackages ∧ ∀ l ∈ s.base.liveRoots, (s.base.root l).package ≠ result
  fresh_facts : FreshStructuralFacts s.base (affectedBy s.base t) fresh
  write_allowed : canWrite
  types_agree : typeCompatible
  post_eq : s' = structuralReplaceCandidate s t incoming result v fresh

def StructuralReplaceStep (canWrite typeCompatible : Prop) (s : CurrentState)
    (t : StructuralTarget) (incoming result : PackageId) (v : StructuredValue)
    (fresh : NodeKey → ValueFactId) (s' : CurrentState) : Prop :=
  CurrentWellFormed s ∧ RawStructuralReplace canWrite typeCompatible s t incoming result v fresh s' ∧
  CurrentWellFormed s'

section
variable {w ty : Prop} {s s' : CurrentState} {t : StructuralTarget}
  {incoming result : PackageId} {v : StructuredValue} {fresh : NodeKey → ValueFactId}

theorem replace_preserves_wellFormed
    (step : StructuralReplaceStep w ty s t incoming result v fresh s') : CurrentWellFormed s' := step.2.2

theorem replace_post_erases_to_wellFormed_f0
    (step : StructuralReplaceStep w ty s t incoming result v fresh s') :
    F0.WellFormed (eraseToF0 s'.base) := f1_wellFormed_erases_to_f0_wellFormed step.2.2.structural

theorem replace_preserves_layout
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') (l : RootLocationId) :
    (s'.base.root l).layout = (s.base.root l).layout := by rw [raw.post_eq]; rfl

theorem replace_preserves_all_incarnations
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).incarnation = ((s.base.root l).node p).incarnation := by rw [raw.post_eq]; rfl

theorem replace_preserves_governing_domain
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') (l : RootLocationId) :
    (s'.base.root l).governing = (s.base.root l).governing := by rw [raw.post_eq]; rfl

theorem replace_preserves_fixed_support_and_incarnation_history
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') :
    s'.base.liveRoots = s.base.liveRoots ∧ s'.base.usedIncarnations = s.base.usedIncarnations ∧
    s'.capability = s.capability ∧ s'.base.liveDomains = s.base.liveDomains ∧
    s'.base.domainValueCarrier = s.base.domainValueCarrier := by rw [raw.post_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem replace_current_fact_equation
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') (l : RootLocationId) (p : PlaceId) :
    ((s'.base.root l).node p).currentFact = if (l,p) ∈ affectedBy s.base t
      then fresh (l,p) else ((s.base.root l).node p).currentFact := by rw [raw.post_eq]; rfl

theorem replace_freshens_affected
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {l : RootLocationId} {p : PlaceId}
    (affected : (l,p) ∈ affectedBy s.base t) :
    ((s'.base.root l).node p).currentFact = fresh (l,p) ∧ fresh (l,p) ∉ s.base.usedValueFacts ∧
    fresh (l,p) ∈ s'.base.usedValueFacts := by
  classical
  refine ⟨?_, raw.fresh_facts.1 _ affected, ?_⟩
  · rw [replace_current_fact_equation raw, ite_eq_left affected]
  · rw [raw.post_eq]; exact refresh_records_new_facts affected

theorem replace_freshens_target (raw : RawStructuralReplace w ty s t incoming result v fresh s') :
    ((s'.base.root t.location).node t.place).currentFact = fresh (t.location,t.place) :=
  (replace_freshens_affected raw (target_is_affected raw.target_live)).1

theorem replace_freshens_ancestors (raw : RawStructuralReplace w ty s t incoming result v fresh s')
    {p : PlaceId} (live : LiveNode s.base t.location p)
    (ancestor : Ancestor (s.base.root t.location).layout p t.place) :
    ((s'.base.root t.location).node p).currentFact = fresh (t.location,p) :=
  (replace_freshens_affected raw (ancestor_of_target_is_affected live ancestor)).1

theorem replace_freshens_descendants (raw : RawStructuralReplace w ty s t incoming result v fresh s')
    {p : PlaceId} (live : LiveNode s.base t.location p)
    (descendant : Ancestor (s.base.root t.location).layout t.place p) :
    ((s'.base.root t.location).node p).currentFact = fresh (t.location,p) :=
  (replace_freshens_affected raw (descendant_of_target_is_affected live descendant)).1

theorem replace_preserves_known_disjoint_current_facts
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {p : PlaceId}
    (live : LiveNode s.base t.location p) (disjoint : KnownDisjoint (s.base.root t.location).layout t.place p) :
    ((s'.base.root t.location).node p).currentFact = ((s.base.root t.location).node p).currentFact := by
  rw [replace_current_fact_equation raw, ite_eq_right (known_disjoint_live_node_is_not_affected live disjoint)]

theorem replace_history_monotone (raw : RawStructuralReplace w ty s t incoming result v fresh s') :
    s.base.usedValueFacts ⊆ s'.base.usedValueFacts := by rw [raw.post_eq]; exact refresh_history_monotone _ _ _

theorem replace_old_affected_facts_not_live (wf : CurrentWellFormed s)
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t) :
    Fact.valueFact p ((s.base.root l).node p).currentFact ∉ StructuralLiveFacts s'.base := by
  rw [raw.post_eq]
  exact refreshed_old_fact_not_live wf.structural raw.fresh_facts live affected

theorem replace_preserves_disjoint_live_facts
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {p : PlaceId}
    (live : LiveNode s.base t.location p) (disjoint : KnownDisjoint (s.base.root t.location).layout t.place p) :
    Fact.valueFact p ((s.base.root t.location).node p).currentFact ∈ StructuralLiveFacts s'.base := by
  refine ⟨t.location, ?_, ?_, replace_preserves_known_disjoint_current_facts raw live disjoint⟩
  · rw [raw.post_eq]; exact live.1
  · rw [replace_preserves_layout raw]; exact live.2

theorem replace_old_value_survives
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') :
    result ∈ s'.base.loosePackages ∧ s'.carried result = some (extractValue s t) ∧
    s'.base.looseValues result = some (extractValue s t).summary := by
  classical
  rw [raw.post_eq]; simp [structuralReplaceCandidate]

theorem replace_installs_new_value
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root t.location) t.place) :
    LocalDeps (s'.base.root t.location) q =
      (v.fragment (relativePosition (s.base.root t.location) t.place q)).dependencies ∧
    s'.content t.location q = (v.fragment (relativePosition (s.base.root t.location) t.place q)).content := by
  classical
  rw [raw.post_eq]; simp [structuralReplaceCandidate, installValue, LocalDeps, inside]

theorem replace_preserves_local_fragments_outside_target
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {l : RootLocationId} {q : PlaceId}
    (outside : ¬ (l = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place)) :
    LocalDeps (s'.base.root l) q = LocalDeps (s.base.root l) q ∧ s'.content l q = s.content l q := by
  classical
  rw [raw.post_eq]; simp [structuralReplaceCandidate, installValue, LocalDeps, outside]

theorem replace_rejects_old_result_invalidated_dependency
    (wf : CurrentWellFormed s) {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ (extractValue s t).dependencies) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh s' := by
  intro step
  rcases replace_old_value_survives step.2.1 with ⟨loose, _, value⟩
  exact replace_old_affected_facts_not_live wf step.2.1 live affected
    (step.2.2.structural.looseDependenciesValid result loose _ value _ dependency)

theorem replace_rejects_incoming_invalidated_dependency
    (wf : CurrentWellFormed s) {l : RootLocationId} {p q : PlaceId}
    (live : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t)
    (inside : q ∈ subtreePlaces (s.base.root t.location) t.place)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      (v.fragment (relativePosition (s.base.root t.location) t.place q)).dependencies) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh s' := by
  classical
  intro step
  apply replace_old_affected_facts_not_live wf step.2.1 live affected
  apply step.2.2.structural.localDependenciesValid t.location q
  · rw [step.2.1.post_eq]; exact ⟨step.2.1.target_live.1, (Finset.mem_filter.mp inside).1⟩
  · rw [(replace_installs_new_value step.2.1 inside).1]; exact dependency


theorem replace_installs_complete_structured_value
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root t.location) t.place) :
    LocalDeps (s'.base.root t.location) q =
      (v.fragment (relativePosition (s.base.root t.location) t.place q)).dependencies ∧
    s'.content t.location q = (v.fragment (relativePosition (s.base.root t.location) t.place q)).content ∧
    s'.capability t.location q = v.discardable (relativePosition (s.base.root t.location) t.place q) := by
  have installed := replace_installs_new_value raw inside
  refine ⟨installed.1,installed.2,?_⟩
  rw [raw.post_eq]; exact (raw.fits.2 q inside).symm

theorem replace_consumes_incoming_loose_carrier (wf : CurrentWellFormed s)
    (raw : RawStructuralReplace w ty s t incoming result v fresh s') : incoming ∉ s'.base.loosePackages := by
  classical
  have resultNotLoose : result ∉ s.base.loosePackages := by
    by_cases rootTarget : t.place = (s.base.root t.location).layout.root
    · have eq : result = (s.base.root t.location).package := by simpa [rootTarget] using raw.result_identity
      rw [eq]; exact wf.structural.installedNotLoose t.location raw.target_live.1
    · have h := raw.result_identity; simp only [ite_eq_right rootTarget] at h; exact h.1
  have different : incoming ≠ result := fun eq => resultNotLoose (eq ▸ raw.incoming_loose)
  rw [raw.post_eq]; simp [structuralReplaceCandidate,installValue,different]

theorem replace_preserves_enclosing_root_carrier_for_subobject
    (raw : RawStructuralReplace w ty s t incoming result v fresh s')
    (subobject : t.place ≠ (s.base.root t.location).layout.root) :
    (s'.base.root t.location).package = (s.base.root t.location).package := by
  classical
  rw [raw.post_eq]; simp [structuralReplaceCandidate,installValue,subobject]

theorem replace_root_carrier_becomes_incoming
    (raw : RawStructuralReplace w ty s t incoming result v fresh s')
    (rootTarget : t.place = (s.base.root t.location).layout.root) :
    (s'.base.root t.location).package = incoming := by
  classical
  rw [raw.post_eq]; simp [structuralReplaceCandidate,installValue,rootTarget]


theorem replace_rejects_other_surviving_invalidated_dependency
    (wf : CurrentWellFormed s) {l m : RootLocationId} {p q : PlaceId}
    (source : LiveNode s.base l p) (affected : (l,p) ∈ affectedBy s.base t)
    (survivor : LiveNode s.base m q)
    (outside : ¬ (m = t.location ∧ q ∈ subtreePlaces (s.base.root t.location) t.place))
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ LocalDeps (s.base.root m) q) :
    ¬ StructuralReplaceStep w ty s t incoming result v fresh s' := by
  intro step
  apply replace_old_affected_facts_not_live wf step.2.1 source affected
  apply step.2.2.structural.localDependenciesValid m q
  · rw [step.2.1.post_eq]; exact survivor
  · rw [(replace_preserves_local_fragments_outside_target step.2.1 outside).1]; exact dependency

end
end
end NewLang.F1
