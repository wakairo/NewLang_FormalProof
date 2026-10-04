import NewLang.F0.WellFormed

namespace NewLang.F0

/-- Atomic structural candidate. Payload/dependency data and domains do not move with roots. -/
def replaceCandidate (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) : State where
  occupancy := fun l =>
    if l = location then .live { root with currentFact := newFact, package := incoming }
    else s.occupancy l
  packages := s.packages
  loosePackages := insert root.package (s.loosePackages.erase incoming)
  liveDomains := s.liveDomains
  usedValueFacts := insert newFact s.usedValueFacts

/-- Replace-only raw relation. The two Prop parameters are caller-supplied static obligations,
not universally valid capabilities. No lifetime-ending/exclusive authority is required.
The old root is a pre-state witness; the result package is `root.package`. -/
structure RawReplace (canWrite typeCompatible : Prop)
    (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) (s' : State) : Prop where
  target_live : s.occupancy location = .live root
  incoming_loose : incoming ∈ s.loosePackages
  fresh : FreshValueFact s newFact
  write_allowed : canWrite
  types_agree : typeCompatible
  post_eq : s' = replaceCandidate s location root incoming newFact

/-- Candidate post-state well-formedness is the central legality check. -/
def ReplaceStep (canWrite typeCompatible : Prop)
    (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) (s' : State) : Prop :=
  WellFormed s ∧ RawReplace canWrite typeCompatible s location root incoming newFact s' ∧
    WellFormed s'

section
variable {canWrite typeCompatible : Prop} {s s' : State} {location : RootLocationId}
  {root : LiveRoot} {incoming : PackageId} {newFact : ValueFactId}

theorem RawReplace.target_after
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    s'.occupancy location = .live { root with currentFact := newFact, package := incoming } := by
  rw [h.post_eq]
  simp [replaceCandidate]

theorem RawReplace.packages_unchanged
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    s'.packages = s.packages := by rw [h.post_eq]; rfl

theorem RawReplace.incoming_ne_old (wf : WellFormed s)
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    incoming ≠ root.package := by
  intro same
  have installed : Carries s incoming (.installed location) :=
    ⟨root, h.target_live, same.symm⟩
  have impossible := wf.carrierUnique incoming (.installed location) .loose
    installed h.incoming_loose
  cases impossible

theorem RawReplace.newFact_ne_old (wf : WellFormed s)
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    newFact ≠ root.currentFact := by
  intro same
  apply h.fresh
  rw [same]
  exact wf.valueFactsRecorded location root h.target_live

/-- History grows even when the old fact becomes dead; no prior allocation is forgotten. -/
theorem replace_history_monotone
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    s.usedValueFacts ⊆ s'.usedValueFacts := by
  rw [h.post_eq]
  exact Finset.subset_insert _ _

theorem replace_preserves_wellFormed
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    WellFormed s' := h.2.2

theorem replace_preserves_incarnation
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.incarnation = root.incarnation :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem replace_preserves_governingDomain
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.governing = root.governing :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem replace_preserves_place_and_location
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.place = root.place :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem replace_preserves_other_locations
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s')
    {other : RootLocationId} (different : other ≠ location) :
    s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]
  simp [replaceCandidate, different]

theorem replace_preserves_package_data_and_domains
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    s'.packages = s.packages ∧ s'.liveDomains = s.liveDomains := by
  rw [h.post_eq]
  exact ⟨rfl, rfl⟩

theorem replace_creates_fresh_current_fact
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    FreshValueFact s newFact ∧ newFact ∈ s'.usedValueFacts ∧
      ∃ after, s'.occupancy location = .live after ∧ after.currentFact = newFact := by
  refine ⟨h.2.1.fresh, ?_, _, h.2.1.target_after, rfl⟩
  rw [h.2.1.post_eq]
  simp [replaceCandidate]

theorem replace_old_fact_remains_used
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    root.currentFact ∈ s'.usedValueFacts :=
  replace_history_monotone h.2.1 (h.1.valueFactsRecorded location root h.2.1.target_live)

theorem replace_old_package_survives_as_loose
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    root.package ∈ s'.loosePackages ∧ Survives s' root.package := by
  have loose : root.package ∈ s'.loosePackages := by
    rw [h.post_eq]
    simp [replaceCandidate]
  exact ⟨loose, Or.inr loose⟩

theorem replace_new_package_installed
    (h : ReplaceStep canWrite typeCompatible s location root incoming newFact s') :
    Carries s' incoming (.installed location) ∧ incoming ∉ s'.loosePackages := by
  refine ⟨⟨_, h.2.1.target_after, rfl⟩, ?_⟩
  rw [h.2.1.post_eq]
  simp [replaceCandidate, h.2.1.incoming_ne_old h.1]

/-- Substantive invalidation lemma: no other root can keep the target's old fact live. -/
theorem rawReplace_old_current_fact_not_live (wf : WellFormed s)
    (h : RawReplace canWrite typeCompatible s location root incoming newFact s') :
    Fact.valueFact root.place root.currentFact ∉ LiveFacts s' := by
  rintro ⟨other, after, live, place, fact⟩
  by_cases same : other = location
  · subst other
    have roots := Occupancy.live.inj (h.target_after.symm.trans live)
    have fresh_eq : newFact = root.currentFact := by
      simpa [← roots] using fact
    exact h.newFact_ne_old wf fresh_eq
  · have pre_live : s.occupancy other = .live after := by
      rw [h.post_eq] at live
      simpa [replaceCandidate, same] using live
    exact same (wf.placesUnique other location after root pre_live h.target_live place)

theorem replace_rejects_surviving_old_current_dependency
    (wf : WellFormed s) {value : ValuePackage}
    (present : s.packages root.package = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ ReplaceStep canWrite typeCompatible s location root incoming newFact s' := by
  intro step
  have post_present : s'.packages root.package = some value := by
    rw [step.2.1.packages_unchanged]
    exact present
  have survivor := (replace_old_package_survives_as_loose step.2.1).2
  have live := step.2.2.dependenciesValid root.package value survivor post_present _ dependency
  exact rawReplace_old_current_fact_not_live wf step.2.1 live

theorem replace_rejects_incoming_old_current_dependency
    (wf : WellFormed s) {value : ValuePackage}
    (present : s.packages incoming = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ ReplaceStep canWrite typeCompatible s location root incoming newFact s' := by
  intro step
  have post_present : s'.packages incoming = some value := by
    rw [step.2.1.packages_unchanged]
    exact present
  have survivor : Survives s' incoming :=
    Or.inl ⟨location, (replace_new_package_installed step).1⟩
  have live := step.2.2.dependenciesValid incoming value survivor post_present _ dependency
  exact rawReplace_old_current_fact_not_live wf step.2.1 live

/-- Applies to all used IDs, including retired IDs that are no longer live anywhere. -/
theorem replace_rejects_previously_used_fact (used : newFact ∈ s.usedValueFacts) :
    ¬ RawReplace canWrite typeCompatible s location root incoming newFact s' := by
  intro raw
  exact raw.fresh used

end
end NewLang.F0
