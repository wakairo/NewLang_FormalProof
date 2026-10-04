import NewLang.F0.WellFormed

namespace NewLang.F0

/-- Fixed proof context for typed occupancy sites. Keep this layout fixed across an execution.
Nominal IDs stay distinct; this association is not backing geometry or a runtime layout. -/
structure RootSiteLayout where
  placeAt : RootLocationId → PlaceId
  injective : Function.Injective placeAt

/-- Derived root-state governing relation; it is never stored in a value package. -/
def Governs (s : State) (incarnation : IncarnationId) (domain : DomainId) : Prop :=
  ∃ location root, s.occupancy location = .live root ∧
    root.incarnation = incarnation ∧ root.governing = domain

def initializeRoot (sites : RootSiteLayout) (location : RootLocationId) (pkg : PackageId)
    (domain : DomainId) (incarnation : IncarnationId) (fact : ValueFactId) : LiveRoot :=
  ⟨sites.placeAt location, incarnation, fact, pkg, domain⟩

def initializeCandidate (sites : RootSiteLayout) (s : State) (location : RootLocationId)
    (pkg : PackageId) (domain : DomainId) (incarnation : IncarnationId) (fact : ValueFactId) : State where
  occupancy := fun l => if l = location then .live (initializeRoot sites location pkg domain incarnation fact)
    else s.occupancy l
  packages := s.packages
  loosePackages := s.loosePackages.erase pkg
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := insert fact s.usedValueFacts
  usedIncarnations := insert incarnation s.usedIncarnations

structure RawInitialize (sites : RootSiteLayout) (canInitialize typeCompatible : Prop)
    (s : State) (location : RootLocationId) (pkg : PackageId) (domain : DomainId)
    (incarnation : IncarnationId) (fact : ValueFactId) (s' : State) : Prop where
  target_vacant : s.occupancy location = .vacant
  incoming_loose : pkg ∈ s.loosePackages
  domain_live : domain ∈ s.liveDomains
  fresh_incarnation : FreshIncarnation s incarnation
  fresh_fact : FreshValueFact s fact
  initialize_allowed : canInitialize
  types_agree : typeCompatible
  post_eq : s' = initializeCandidate sites s location pkg domain incarnation fact

def InitializeStep (sites : RootSiteLayout) (ci tc : Prop) (s : State)
    (location : RootLocationId) (pkg : PackageId) (domain : DomainId)
    (incarnation : IncarnationId) (fact : ValueFactId) (s' : State) : Prop :=
  WellFormed s ∧ RawInitialize sites ci tc s location pkg domain incarnation fact s' ∧ WellFormed s'

/-- Return the value carrier and vacancy together; the histories/domain remain live. -/
def takeCandidate (s : State) (location : RootLocationId) (root : LiveRoot) : State where
  occupancy := fun l => if l = location then .vacant else s.occupancy l
  packages := s.packages
  loosePackages := insert root.package s.loosePackages
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := s.usedValueFacts
  usedIncarnations := s.usedIncarnations

/-- One combined end-and-discard candidate, never a legal take followed by discard. -/
def destroyCandidate (s : State) (location : RootLocationId) (root : LiveRoot) : State where
  occupancy := fun l => if l = location then .vacant else s.occupancy l
  packages := s.packages
  loosePackages := s.loosePackages.erase root.package
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := s.usedValueFacts
  usedIncarnations := s.usedIncarnations

structure RawTake (canEndRoot : Prop) (s : State) (location : RootLocationId)
    (root : LiveRoot) (endingDomain : DomainId) (s' : State) : Prop where
  target_live : s.occupancy location = .live root
  domain_matches : endingDomain = root.governing
  ending_allowed : canEndRoot
  post_eq : s' = takeCandidate s location root

structure RawDestroy (canEndRoot : Prop) (s : State) (location : RootLocationId)
    (root : LiveRoot) (endingDomain : DomainId) (s' : State) : Prop where
  target_live : s.occupancy location = .live root
  domain_matches : endingDomain = root.governing
  ending_allowed : canEndRoot
  old_discardable : ∃ value, s.packages root.package = some value ∧ value.discardable = true
  post_eq : s' = destroyCandidate s location root

def TakeStep (ce : Prop) (s : State) (location : RootLocationId) (root : LiveRoot)
    (endingDomain : DomainId) (s' : State) : Prop :=
  WellFormed s ∧ RawTake ce s location root endingDomain s' ∧ WellFormed s'
def DestroyStep (ce : Prop) (s : State) (location : RootLocationId) (root : LiveRoot)
    (endingDomain : DomainId) (s' : State) : Prop :=
  WellFormed s ∧ RawDestroy ce s location root endingDomain s' ∧ WellFormed s'

section Initialize
variable {sites : RootSiteLayout} {ci tc : Prop} {s s' : State} {location : RootLocationId}
  {pkg : PackageId} {domain : DomainId} {incarnation : IncarnationId} {fact : ValueFactId}

theorem RawInitialize.target_after
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    s'.occupancy location = .live (initializeRoot sites location pkg domain incarnation fact) := by
  rw [h.post_eq]; simp [initializeCandidate]

theorem initialize_preserves_wellFormed
    (h : InitializeStep sites ci tc s location pkg domain incarnation fact s') : WellFormed s' := h.2.2

theorem initialize_consumes_vacancy
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    s.occupancy location = .vacant ∧ s'.occupancy location ≠ .vacant := by
  exact ⟨h.target_vacant, by rw [h.target_after]; simp⟩

theorem initialize_installs_package
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    Carries s' pkg (.installed location) ∧ pkg ∉ s'.loosePackages := by
  refine ⟨⟨_, h.target_after, rfl⟩, ?_⟩
  rw [h.post_eq]; simp [initializeCandidate]

theorem initialize_package_unique_installed_carrier
    (h : InitializeStep sites ci tc s location pkg domain incarnation fact s') :
    ∀ carrier, Carries s' pkg carrier → carrier = .installed location := by
  intro carrier carries
  exact h.2.2.carrierUnique pkg carrier (.installed location) carries (initialize_installs_package h.2.1).1

theorem initialize_incarnation_history_monotone
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    s.usedIncarnations ⊆ s'.usedIncarnations := by
  rw [h.post_eq]; exact Finset.subset_insert _ _

theorem initialize_value_fact_history_monotone
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    s.usedValueFacts ⊆ s'.usedValueFacts := by
  rw [h.post_eq]; exact Finset.subset_insert _ _

theorem initialize_creates_fresh_incarnation
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    FreshIncarnation s incarnation ∧ incarnation ∈ s'.usedIncarnations ∧ LiveIncarnation s' incarnation := by
  refine ⟨h.fresh_incarnation, ?_, location, _, h.target_after, rfl⟩
  rw [h.post_eq]; simp [initializeCandidate]

theorem initialize_creates_fresh_current_fact
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    FreshValueFact s fact ∧ fact ∈ s'.usedValueFacts ∧
    Fact.valueFact (sites.placeAt location) fact ∈ LiveFacts s' := by
  refine ⟨h.fresh_fact, ?_, location, _, h.target_after, rfl, rfl⟩
  rw [h.post_eq]; simp [initializeCandidate]

theorem initialize_creates_governing_relation
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    Governs s' incarnation domain ∧
    (initializeRoot sites location pkg domain incarnation fact).governing = domain :=
  ⟨⟨location, _, h.target_after, rfl, rfl⟩, rfl⟩

theorem initialize_uses_stable_site_place
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    ∃ root, s'.occupancy location = .live root ∧ root.place = sites.placeAt location :=
  ⟨_, h.target_after, rfl⟩

theorem initialize_preserves_other_locations
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s')
    {other : RootLocationId} (different : other ≠ location) : s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]; simp [initializeCandidate, different]

theorem initialize_preserves_package_data
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') : s'.packages = s.packages := by
  rw [h.post_eq]; rfl

theorem initialize_preserves_live_domains
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') : s'.liveDomains = s.liveDomains := by
  rw [h.post_eq]; rfl

theorem initialize_rejects_reused_incarnation (used : incarnation ∈ s.usedIncarnations) :
    ¬ RawInitialize sites ci tc s location pkg domain incarnation fact s' := by
  intro h; exact h.fresh_incarnation used

theorem initialize_rejects_reused_current_fact (used : fact ∈ s.usedValueFacts) :
    ¬ RawInitialize sites ci tc s location pkg domain incarnation fact s' := by
  intro h; exact h.fresh_fact used

theorem initialize_rejects_dead_domain (dead : domain ∉ s.liveDomains) :
    ¬ RawInitialize sites ci tc s location pkg domain incarnation fact s' := by
  intro h; exact dead h.domain_live

theorem initialize_rejects_missing_authority (missing : ¬ ci) :
    ¬ RawInitialize sites ci tc s location pkg domain incarnation fact s' := by
  intro h; exact missing h.initialize_allowed

theorem initialize_preserves_domain_carriers
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s') :
    s'.domainValueCarrier = s.domainValueCarrier := by rw [h.post_eq]; rfl

end Initialize

section EndRoot
variable {ce : Prop} {s s' : State} {location : RootLocationId} {root : LiveRoot} {domain : DomainId}

theorem take_preserves_wellFormed (h : TakeStep ce s location root domain s') : WellFormed s' := h.2.2

theorem take_restores_vacancy (h : RawTake ce s location root domain s') :
    s'.occupancy location = .vacant := by rw [h.post_eq]; simp [takeCandidate]

theorem take_preserves_other_locations (h : RawTake ce s location root domain s')
    {other : RootLocationId} (different : other ≠ location) : s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]; simp [takeCandidate, different]

theorem take_preserves_package_data (h : RawTake ce s location root domain s') :
    s'.packages = s.packages := by rw [h.post_eq]; rfl

theorem take_preserves_live_domains (h : RawTake ce s location root domain s') :
    s'.liveDomains = s.liveDomains := by rw [h.post_eq]; rfl

theorem take_preserves_identity_histories (h : RawTake ce s location root domain s') :
    s'.usedIncarnations = s.usedIncarnations ∧ s'.usedValueFacts = s.usedValueFacts := by
  rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem take_ended_identities_remain_recorded (wf : WellFormed s)
    (h : RawTake ce s location root domain s') :
    root.incarnation ∈ s'.usedIncarnations ∧ root.currentFact ∈ s'.usedValueFacts := by
  rw [(take_preserves_identity_histories h).1, (take_preserves_identity_histories h).2]
  exact ⟨wf.incarnationsRecorded location root h.target_live,
    wf.valueFactsRecorded location root h.target_live⟩

theorem take_ends_incarnation (wf : WellFormed s) (h : RawTake ce s location root domain s') :
    ¬ LiveIncarnation s' root.incarnation := by
  rintro ⟨other, after, live, incarnation⟩
  by_cases same : other = location
  · subst other; rw [take_restores_vacancy h] at live; cases live
  · have pre_live := (take_preserves_other_locations h same).symm.trans live
    exact same (wf.incarnationsUnique other location after root pre_live h.target_live incarnation)

theorem take_old_current_fact_not_live (wf : WellFormed s)
    (h : RawTake ce s location root domain s') : Fact.valueFact root.place root.currentFact ∉ LiveFacts s' := by
  rintro ⟨other, after, live, place, _⟩
  by_cases same : other = location
  · subst other; rw [take_restores_vacancy h] at live; cases live
  · have pre_live := (take_preserves_other_locations h same).symm.trans live
    exact same (wf.placesUnique other location after root pre_live h.target_live place)

theorem take_ends_governing_relation (wf : WellFormed s)
    (h : RawTake ce s location root domain s') : ∀ d, ¬ Governs s' root.incarnation d := by
  rintro d ⟨other, after, live, incarnation, _⟩
  exact take_ends_incarnation wf h ⟨other, after, live, incarnation⟩

theorem take_does_not_finalize_domain (wf : WellFormed s)
    (h : RawTake ce s location root domain s') : Fact.domainLive root.governing ∈ LiveFacts s' := by
  change root.governing ∈ s'.liveDomains
  rw [take_preserves_live_domains h]
  exact wf.domainsValid location root h.target_live

theorem take_rejects_wrong_ending_domain (wrong : domain ≠ root.governing) :
    ¬ RawTake ce s location root domain s' := by intro h; exact wrong h.domain_matches

theorem take_rejects_missing_authority (missing : ¬ ce) :
    ¬ RawTake ce s location root domain s' := by intro h; exact missing h.ending_allowed

theorem destroy_preserves_wellFormed (h : DestroyStep ce s location root domain s') : WellFormed s' := h.2.2

theorem destroy_restores_vacancy (h : RawDestroy ce s location root domain s') :
    s'.occupancy location = .vacant := by rw [h.post_eq]; simp [destroyCandidate]

theorem destroy_preserves_other_locations (h : RawDestroy ce s location root domain s')
    {other : RootLocationId} (different : other ≠ location) : s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]; simp [destroyCandidate, different]

theorem destroy_preserves_package_data (h : RawDestroy ce s location root domain s') :
    s'.packages = s.packages := by rw [h.post_eq]; rfl

theorem destroy_preserves_live_domains (h : RawDestroy ce s location root domain s') :
    s'.liveDomains = s.liveDomains := by rw [h.post_eq]; rfl

theorem destroy_preserves_identity_histories (h : RawDestroy ce s location root domain s') :
    s'.usedIncarnations = s.usedIncarnations ∧ s'.usedValueFacts = s.usedValueFacts := by
  rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem destroy_ended_identities_remain_recorded (wf : WellFormed s)
    (h : RawDestroy ce s location root domain s') :
    root.incarnation ∈ s'.usedIncarnations ∧ root.currentFact ∈ s'.usedValueFacts := by
  rw [(destroy_preserves_identity_histories h).1, (destroy_preserves_identity_histories h).2]
  exact ⟨wf.incarnationsRecorded location root h.target_live,
    wf.valueFactsRecorded location root h.target_live⟩

theorem destroy_ends_incarnation (wf : WellFormed s) (h : RawDestroy ce s location root domain s') :
    ¬ LiveIncarnation s' root.incarnation := by
  rintro ⟨other, after, live, incarnation⟩
  by_cases same : other = location
  · subst other; rw [destroy_restores_vacancy h] at live; cases live
  · have pre_live := (destroy_preserves_other_locations h same).symm.trans live
    exact same (wf.incarnationsUnique other location after root pre_live h.target_live incarnation)

theorem destroy_old_current_fact_not_live (wf : WellFormed s)
    (h : RawDestroy ce s location root domain s') : Fact.valueFact root.place root.currentFact ∉ LiveFacts s' := by
  rintro ⟨other, after, live, place, _⟩
  by_cases same : other = location
  · subst other; rw [destroy_restores_vacancy h] at live; cases live
  · have pre_live := (destroy_preserves_other_locations h same).symm.trans live
    exact same (wf.placesUnique other location after root pre_live h.target_live place)

theorem destroy_ends_governing_relation (wf : WellFormed s)
    (h : RawDestroy ce s location root domain s') : ∀ d, ¬ Governs s' root.incarnation d := by
  rintro d ⟨other, after, live, incarnation, _⟩
  exact destroy_ends_incarnation wf h ⟨other, after, live, incarnation⟩

theorem destroy_does_not_finalize_domain (wf : WellFormed s)
    (h : RawDestroy ce s location root domain s') : Fact.domainLive root.governing ∈ LiveFacts s' := by
  change root.governing ∈ s'.liveDomains
  rw [destroy_preserves_live_domains h]
  exact wf.domainsValid location root h.target_live

theorem destroy_rejects_wrong_ending_domain (wrong : domain ≠ root.governing) :
    ¬ RawDestroy ce s location root domain s' := by intro h; exact wrong h.domain_matches

theorem destroy_rejects_missing_authority (missing : ¬ ce) :
    ¬ RawDestroy ce s location root domain s' := by intro h; exact missing h.ending_allowed

theorem take_old_package_survives_as_loose (h : RawTake ce s location root domain s') :
    Carries s' root.package .loose ∧ Survives s' root.package := by
  have loose : root.package ∈ s'.loosePackages := by rw [h.post_eq]; simp [takeCandidate]
  exact ⟨loose, Or.inr loose⟩

theorem take_old_package_unique_loose_carrier (h : TakeStep ce s location root domain s') :
    ∀ carrier, Carries s' root.package carrier → carrier = .loose := by
  intro carrier carries
  exact h.2.2.carrierUnique root.package carrier .loose carries (take_old_package_survives_as_loose h.2.1).1

theorem take_survivors_preserved (h : RawTake ce s location root domain s')
    {pkg : PackageId} (survivor : Survives s pkg) : Survives s' pkg := by
  rcases survivor with ⟨other, after, live, package⟩ | loose
  · by_cases same : other = location
    · subst other
      have roots := Occupancy.live.inj (h.target_live.symm.trans live)
      subst after; rw [← package]; exact (take_old_package_survives_as_loose h).2
    · exact Or.inl ⟨other, after, (take_preserves_other_locations h same).trans live, package⟩
  · exact Or.inr (by rw [h.post_eq]; exact Finset.mem_insert_of_mem loose)

theorem take_rejects_surviving_old_current_dependency (wf : WellFormed s)
    {pkg : PackageId} {value : ValuePackage} (survivor : Survives s pkg)
    (present : s.packages pkg = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ TakeStep ce s location root domain s' := by
  intro step
  have post_present : s'.packages pkg = some value := by rw [take_preserves_package_data step.2.1]; exact present
  have live := step.2.2.dependenciesValid pkg value (take_survivors_preserved step.2.1 survivor)
    post_present _ dependency
  exact take_old_current_fact_not_live wf step.2.1 live

theorem take_rejects_old_self_current_dependency (wf : WellFormed s)
    (live : s.occupancy location = .live root) {value : ValuePackage}
    (present : s.packages root.package = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ TakeStep ce s location root domain s' :=
  take_rejects_surviving_old_current_dependency wf (Or.inl ⟨location, root, live, rfl⟩) present dependency

theorem destroy_old_package_does_not_survive (wf : WellFormed s)
    (h : RawDestroy ce s location root domain s') : ¬ Survives s' root.package := by
  rintro (⟨other, after, live, package⟩ | loose)
  · by_cases same : other = location
    · subst other; rw [destroy_restores_vacancy h] at live; cases live
    · have pre_live := (destroy_preserves_other_locations h same).symm.trans live
      have unique := wf.carrierUnique root.package (.installed other) (.installed location)
        ⟨after, pre_live, package⟩ ⟨root, h.target_live, rfl⟩
      exact same (Carrier.installed.inj unique)
  · rw [h.post_eq] at loose; simp [destroyCandidate] at loose

theorem destroy_other_survivors_preserved (h : RawDestroy ce s location root domain s')
    {pkg : PackageId} (survivor : Survives s pkg) (different : pkg ≠ root.package) : Survives s' pkg := by
  rcases survivor with ⟨other, after, live, package⟩ | loose
  · have other_ne : other ≠ location := by
      intro same; subst other
      have roots := Occupancy.live.inj (h.target_live.symm.trans live)
      exact different (by simpa [← roots] using package.symm)
    exact Or.inl ⟨other, after, (destroy_preserves_other_locations h other_ne).trans live, package⟩
  · exact Or.inr (by rw [h.post_eq]; simpa [destroyCandidate, different] using loose)

theorem destroy_rejects_other_surviving_old_current_dependency (wf : WellFormed s)
    {pkg : PackageId} {value : ValuePackage} (survivor : Survives s pkg) (different : pkg ≠ root.package)
    (present : s.packages pkg = some value)
    (dependency : Fact.valueFact root.place root.currentFact ∈ value.dependencies) :
    ¬ DestroyStep ce s location root domain s' := by
  intro step
  have post_present : s'.packages pkg = some value := by rw [destroy_preserves_package_data step.2.1]; exact present
  have live := step.2.2.dependenciesValid pkg value (destroy_other_survivors_preserved step.2.1 survivor different)
    post_present _ dependency
  exact destroy_old_current_fact_not_live wf step.2.1 live

theorem destroy_requires_discardable_old_package (h : DestroyStep ce s location root domain s') :
    ∃ value, s.packages root.package = some value ∧ value.discardable = true := h.2.1.old_discardable

theorem destroy_rejects_nondiscardable_old_package {value : ValuePackage}
    (present : s.packages root.package = some value) (nondiscardable : value.discardable = false) :
    ¬ RawDestroy ce s location root domain s' := by
  intro h
  rcases h.old_discardable with ⟨actual, defined, allowed⟩
  have same := Option.some.inj (present.symm.trans defined)
  simp [← same, nondiscardable] at allowed

theorem take_preserves_domain_carriers (h : RawTake ce s location root domain s') :
    s'.domainValueCarrier = s.domainValueCarrier := by rw [h.post_eq]; rfl

theorem destroy_preserves_domain_carriers (h : RawDestroy ce s location root domain s') :
    s'.domainValueCarrier = s.domainValueCarrier := by rw [h.post_eq]; rfl

end EndRoot
end NewLang.F0
