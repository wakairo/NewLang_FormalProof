import NewLang.F0.WellFormed

namespace NewLang.F0

/-- One atomic candidate: the old carrier is consumed, never returned as a loose result.
Uncarried package records may remain in the table; they are not surviving values. -/
def storeCandidate (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) : State where
  occupancy := fun l =>
    if l = location then .live { root with currentFact := newFact, package := incoming }
    else s.occupancy l
  packages := s.packages
  loosePackages := (s.loosePackages.erase incoming).erase root.package
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := insert newFact s.usedValueFacts
  usedIncarnations := s.usedIncarnations

/-- Store-only raw relation. Discardability applies to the old package, not the incoming one.
Write/type obligations are caller-supplied propositions; no lifetime-ending authority is used. -/
structure RawStore (canWrite typeCompatible : Prop)
    (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) (s' : State) : Prop where
  target_live : s.occupancy location = .live root
  incoming_loose : incoming ∈ s.loosePackages
  fresh : FreshValueFact s newFact
  write_allowed : canWrite
  types_agree : typeCompatible
  old_discardable : ∃ value, s.packages root.package = some value ∧ value.discardable = true
  post_eq : s' = storeCandidate s location root incoming newFact

/-- Legality checks the combined store post-state, without requiring any ReplaceStep. -/
def StoreStep (canWrite typeCompatible : Prop)
    (s : State) (location : RootLocationId) (root : LiveRoot)
    (incoming : PackageId) (newFact : ValueFactId) (s' : State) : Prop :=
  WellFormed s ∧ RawStore canWrite typeCompatible s location root incoming newFact s' ∧
    WellFormed s'

section
variable {canWrite typeCompatible : Prop} {s s' : State} {location : RootLocationId}
  {root : LiveRoot} {incoming : PackageId} {newFact : ValueFactId}

theorem RawStore.target_after
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    s'.occupancy location = .live { root with currentFact := newFact, package := incoming } := by
  rw [h.post_eq]
  simp [storeCandidate]

theorem RawStore.packages_unchanged
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    s'.packages = s.packages := by rw [h.post_eq]; rfl

theorem RawStore.incoming_ne_old (wf : WellFormed s)
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    incoming ≠ root.package := by
  intro same
  have installed : Carries s incoming (.installed location) :=
    ⟨root, h.target_live, same.symm⟩
  have impossible := wf.carrierUnique incoming (.installed location) .loose
    installed h.incoming_loose
  cases impossible

theorem RawStore.newFact_ne_old (wf : WellFormed s)
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    newFact ≠ root.currentFact := by
  intro same
  apply h.fresh
  rw [same]
  exact wf.valueFactsRecorded location root h.target_live

theorem store_history_monotone
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    s.usedValueFacts ⊆ s'.usedValueFacts := by
  rw [h.post_eq]
  exact Finset.subset_insert _ _

theorem store_preserves_wellFormed
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    WellFormed s' := h.2.2

theorem store_preserves_incarnation
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.incarnation = root.incarnation :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem store_preserves_governingDomain
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.governing = root.governing :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem store_preserves_place_and_location
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ after, s'.occupancy location = .live after ∧ after.place = root.place :=
  ⟨_, h.2.1.target_after, rfl⟩

theorem store_preserves_other_locations
    (h : RawStore canWrite typeCompatible s location root incoming newFact s')
    {other : RootLocationId} (different : other ≠ location) :
    s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]
  simp [storeCandidate, different]

theorem store_preserves_package_data_and_domains
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    s'.packages = s.packages ∧ s'.liveDomains = s.liveDomains := by
  rw [h.post_eq]
  exact ⟨rfl, rfl⟩

theorem store_creates_fresh_current_fact
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    FreshValueFact s newFact ∧ newFact ∈ s'.usedValueFacts ∧
      ∃ after, s'.occupancy location = .live after ∧ after.currentFact = newFact := by
  refine ⟨h.2.1.fresh, ?_, _, h.2.1.target_after, rfl⟩
  rw [h.2.1.post_eq]
  simp [storeCandidate]

theorem store_old_fact_remains_used
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    root.currentFact ∈ s'.usedValueFacts :=
  store_history_monotone h.2.1 (h.1.valueFactsRecorded location root h.2.1.target_live)

theorem store_new_package_installed
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    Carries s' incoming (.installed location) ∧ incoming ∉ s'.loosePackages := by
  refine ⟨⟨_, h.target_after, rfl⟩, ?_⟩
  rw [h.post_eq]
  simp [storeCandidate]

/-- Consumption removes every old carrier, including the possibility of another installation. -/
theorem rawStore_old_package_does_not_survive (wf : WellFormed s)
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    ¬ Survives s' root.package := by
  intro survivor
  rcases survivor with installed | loose
  · rcases installed with ⟨other, after, live, pkg⟩
    by_cases same : other = location
    · subst other
      have roots := Occupancy.live.inj (h.target_after.symm.trans live)
      have wrong : incoming = root.package := by simpa [← roots] using pkg
      exact h.incoming_ne_old wf wrong
    · have pre_live : s.occupancy other = .live after := by
        rw [h.post_eq] at live
        simpa [storeCandidate, same] using live
      have carriers := wf.carrierUnique root.package (.installed other) (.installed location)
        ⟨after, pre_live, pkg⟩ ⟨root, h.target_live, rfl⟩
      exact same (Carrier.installed.inj carriers)
  · rw [h.post_eq] at loose
    simp [storeCandidate] at loose

theorem store_old_package_does_not_survive
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    ¬ Survives s' root.package := rawStore_old_package_does_not_survive h.1 h.2.1

/-- All pre-state survivors except the consumed old package remain tracked. -/
theorem store_other_survivors_preserved
    (h : RawStore canWrite typeCompatible s location root incoming newFact s')
    {pkg : PackageId} (survivor : Survives s pkg) (different : pkg ≠ root.package) :
    Survives s' pkg := by
  rcases survivor with installed | loose
  · rcases installed with ⟨other, after, live, package⟩
    have other_ne : other ≠ location := by
      intro same
      subst other
      have roots := Occupancy.live.inj (h.target_live.symm.trans live)
      exact different (by simpa [← roots] using package.symm)
    refine Or.inl ⟨other, after, ?_, package⟩
    rw [h.post_eq]
    simpa [storeCandidate, other_ne] using live
  · by_cases incoming_eq : pkg = incoming
    · subst pkg
      exact Or.inl ⟨location, (store_new_package_installed h).1⟩
    · apply Or.inr
      rw [h.post_eq]
      simpa [storeCandidate, different, incoming_eq] using loose

theorem rawStore_old_current_fact_not_live (wf : WellFormed s)
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    Fact.valueFact root.place root.currentFact ∉ LiveFacts s' := by
  rintro ⟨other, after, live, place, fact⟩
  by_cases same : other = location
  · subst other
    have roots := Occupancy.live.inj (h.target_after.symm.trans live)
    have fresh_eq : newFact = root.currentFact := by simpa [← roots] using fact
    exact h.newFact_ne_old wf fresh_eq
  · have pre_live : s.occupancy other = .live after := by
      rw [h.post_eq] at live
      simpa [storeCandidate, same] using live
    exact same (wf.placesUnique other location after root pre_live h.target_live place)

/-- A dependency is removed only with its carrying package, not globally ignored. -/
theorem store_rejects_other_surviving_old_current_dependency
    (wf : WellFormed s) {pkg : PackageId} {value : ValuePackage}
    (survivor : Survives s pkg) (different : pkg ≠ root.package)
    (present : s.packages pkg = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ StoreStep canWrite typeCompatible s location root incoming newFact s' := by
  intro step
  have post_present : s'.packages pkg = some value := by
    rw [step.2.1.packages_unchanged]
    exact present
  have post_survivor := store_other_survivors_preserved step.2.1 survivor different
  have live := step.2.2.dependenciesValid pkg value post_survivor post_present _ dependency
  exact rawStore_old_current_fact_not_live wf step.2.1 live

theorem store_rejects_incoming_old_current_dependency
    (wf : WellFormed s) {value : ValuePackage}
    (present : s.packages incoming = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ StoreStep canWrite typeCompatible s location root incoming newFact s' := by
  intro step
  have post_present : s'.packages incoming = some value := by
    rw [step.2.1.packages_unchanged]
    exact present
  have survivor : Survives s' incoming := Or.inl ⟨location, (store_new_package_installed step.2.1).1⟩
  have live := step.2.2.dependenciesValid incoming value survivor post_present _ dependency
  exact rawStore_old_current_fact_not_live wf step.2.1 live

theorem store_requires_discardable_old_package
    (h : StoreStep canWrite typeCompatible s location root incoming newFact s') :
    ∃ value, s.packages root.package = some value ∧ value.discardable = true := h.2.1.old_discardable

theorem store_rejects_nondiscardable_old_package {value : ValuePackage}
    (present : s.packages root.package = some value) (nondiscardable : value.discardable = false) :
    ¬ RawStore canWrite typeCompatible s location root incoming newFact s' := by
  intro raw
  rcases raw.old_discardable with ⟨actual, defined, discardable⟩
  have same : value = actual := Option.some.inj (present.symm.trans defined)
  simp [← same, nondiscardable] at discardable

theorem store_rejects_previously_used_fact (used : newFact ∈ s.usedValueFacts) :
    ¬ RawStore canWrite typeCompatible s location root incoming newFact s' := by
  intro raw
  exact raw.fresh used

theorem store_preserves_incarnation_history
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') : s'.usedIncarnations = s.usedIncarnations := by
  rw [h.post_eq]; rfl

theorem store_preserves_domain_carriers
    (h : RawStore canWrite typeCompatible s location root incoming newFact s') :
    s'.domainValueCarrier = s.domainValueCarrier := by rw [h.post_eq]; rfl

end
end NewLang.F0
