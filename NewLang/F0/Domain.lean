import NewLang.F0.Reference

namespace NewLang.F0

/-- Move the value carrier of the same domain identity. No source object geometry. -/
def domainTransferCandidate (s : State) (domain : DomainId) (newCarrier : DomainValueCarrierId) : State :=
  {s with domainValueCarrier := fun d => if d = domain then some newCarrier else s.domainValueCarrier d}

/-- The caller premise includes unmodeled current-domain-value capability conflicts.
DomainLive dependencies and governed roots are not transfer blockers. -/
structure RawDomainTransfer (transferAllowed : Prop) (s : State) (domain : DomainId)
    (oldCarrier newCarrier : DomainValueCarrierId) (s' : State) : Prop where
  domain_live : domain ∈ s.liveDomains
  current_carrier : s.domainValueCarrier domain = some oldCarrier
  transfer_allowed : transferAllowed
  post_eq : s' = domainTransferCandidate s domain newCarrier

def DomainTransferStep (allowed : Prop) (s : State) (domain : DomainId)
    (oldCarrier newCarrier : DomainValueCarrierId) (s' : State) : Prop :=
  WellFormed s ∧ RawDomainTransfer allowed s domain oldCarrier newCarrier s' ∧ WellFormed s'

/-- End D and its value carrier together. Roots/packages/dependencies are not rewritten. -/
def finalizeDomainCandidate (s : State) (domain : DomainId) : State :=
  {s with
    liveDomains := s.liveDomains.erase domain
    domainValueCarrier := fun d => if d = domain then none else s.domainValueCarrier d}

/-- Only omitted scoped-capability/applicability conditions are abstracted.
Modeled governed roots and package dependencies are checked by post-state WellFormed. -/
structure RawFinalizeDomain (canFinalize : Prop) (s : State) (domain : DomainId)
    (carrier : DomainValueCarrierId) (s' : State) : Prop where
  domain_live : domain ∈ s.liveDomains
  current_carrier : s.domainValueCarrier domain = some carrier
  finalize_allowed : canFinalize
  post_eq : s' = finalizeDomainCandidate s domain

def FinalizeDomainStep (allowed : Prop) (s : State) (domain : DomainId)
    (carrier : DomainValueCarrierId) (s' : State) : Prop :=
  WellFormed s ∧ RawFinalizeDomain allowed s domain carrier s' ∧ WellFormed s'

section Transfer
variable {allowed : Prop} {s s' : State} {domain : DomainId} {oldCarrier newCarrier : DomainValueCarrierId}

theorem domain_transfer_preserves_wellFormed
    (h : DomainTransferStep allowed s domain oldCarrier newCarrier s') : WellFormed s' := h.2.2

theorem domain_transfer_preserves_identity
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') : s'.liveDomains = s.liveDomains := by
  rw [h.post_eq]; rfl

theorem domain_transfer_preserves_liveness
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') :
    domain ∈ s.liveDomains ∧ domain ∈ s'.liveDomains := by
  rw [domain_transfer_preserves_identity h]; exact ⟨h.domain_live, h.domain_live⟩

theorem domain_transfer_moves_value_carrier
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') :
    s.domainValueCarrier domain = some oldCarrier ∧ s'.domainValueCarrier domain = some newCarrier := by
  refine ⟨h.current_carrier, ?_⟩; rw [h.post_eq]; simp [domainTransferCandidate]

theorem domain_transfer_preserves_other_carriers
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s')
    {other : DomainId} (different : other ≠ domain) : s'.domainValueCarrier other = s.domainValueCarrier other := by
  rw [h.post_eq]; simp [domainTransferCandidate, different]

theorem domain_transfer_preserves_roots
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') : s'.occupancy = s.occupancy := by
  rw [h.post_eq]; rfl

theorem domain_transfer_preserves_governing_relations
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') (inc : IncarnationId) (d : DomainId) :
    Governs s' inc d ↔ Governs s inc d := by
  simp only [Governs, domain_transfer_preserves_roots h]

theorem domain_transfer_preserves_packages
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') :
    s'.packages = s.packages ∧ s'.loosePackages = s.loosePackages := by rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem domain_transfer_preserves_histories
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') :
    s'.usedValueFacts = s.usedValueFacts ∧ s'.usedIncarnations = s.usedIncarnations := by
  rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem domain_transfer_preserves_liveFacts
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') : LiveFacts s' = LiveFacts s := by
  funext fact; cases fact <;> simp [LiveFacts, domain_transfer_preserves_roots h, domain_transfer_preserves_identity h]

theorem domain_transfer_preserves_survivors
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') (pkg : PackageId) :
    Survives s' pkg ↔ Survives s pkg := by
  simp only [Survives, IsInstalled, Carries, domain_transfer_preserves_roots h,
    (domain_transfer_preserves_packages h).2]

theorem domain_transfer_preserves_DomainLive_dependencies
    (h : DomainTransferStep allowed s domain oldCarrier newCarrier s') {pkg : PackageId} {value : ValuePackage}
    (survivor : Survives s pkg) (present : s.packages pkg = some value)
    (dep : Fact.domainLive domain ∈ value.dependencies) :
    Survives s' pkg ∧ s'.packages pkg = some value ∧ Fact.domainLive domain ∈ LiveFacts s' := by
  exact ⟨(domain_transfer_preserves_survivors h.2.1 pkg).mpr survivor,
    (congrFun (domain_transfer_preserves_packages h.2.1).1 pkg).trans present,
    h.2.2.dependenciesValid pkg value ((domain_transfer_preserves_survivors h.2.1 pkg).mpr survivor)
      ((congrFun (domain_transfer_preserves_packages h.2.1).1 pkg).trans present) _ dep⟩

/-- All modeled transfer frames preserve the invariant; omitted value conflict remains a caller obligation. -/
theorem raw_domain_transfer_preserves_wellFormed (wf : WellFormed s)
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') : WellFormed s' := by
  rw [h.post_eq]
  refine ⟨wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique, wf.packagesPresent,
    wf.domainsValid, wf.dependenciesValid, wf.valueFactsRecorded, wf.incarnationsRecorded, ?_⟩
  intro d
  by_cases same : d = domain
  · subst d; simp [domainTransferCandidate, h.domain_live]
  · simpa [domainTransferCandidate, same] using wf.domainCarrierCoherent d

theorem domain_transfer_step_of_raw (wf : WellFormed s)
    (h : RawDomainTransfer allowed s domain oldCarrier newCarrier s') :
    DomainTransferStep allowed s domain oldCarrier newCarrier s' :=
  ⟨wf, h, raw_domain_transfer_preserves_wellFormed wf h⟩

/-- Fresh caller evidence/access obligations for the post state are explicit.
This is point-of-acquisition preservation, not a claim about an existing ref's scope. -/
theorem domain_transfer_preserves_acquire_ref {stablePre accessPre stablePost accessPost : Prop}
    {ptr : PtrToken} {evidenceDomain : DomainId}
    (h : DomainTransferStep allowed s domain oldCarrier newCarrier s')
    (before : AcquireRef stablePre accessPre s ptr evidenceDomain)
    (evidence : stablePost) (access : accessPost) : AcquireRef stablePost accessPost s' ptr evidenceDomain := by
  refine ⟨h.2.2, ⟨?_, evidence, access⟩⟩
  simpa only [domain_transfer_preserves_roots h.2.1] using before.2.target

theorem domain_transfer_rejects_missing_permission (missing : ¬ allowed) :
    ¬ RawDomainTransfer allowed s domain oldCarrier newCarrier s' := by intro h; exact missing h.transfer_allowed

theorem domain_transfer_rejects_dead_domain (dead : domain ∉ s.liveDomains) :
    ¬ RawDomainTransfer allowed s domain oldCarrier newCarrier s' := by intro h; exact dead h.domain_live

theorem domain_transfer_rejects_wrong_carrier (wrong : s.domainValueCarrier domain ≠ some oldCarrier) :
    ¬ RawDomainTransfer allowed s domain oldCarrier newCarrier s' := by intro h; exact wrong h.current_carrier

end Transfer

section Finalize
variable {allowed : Prop} {s s' : State} {domain : DomainId} {carrier : DomainValueCarrierId}

theorem finalize_domain_preserves_wellFormed (h : FinalizeDomainStep allowed s domain carrier s') :
    WellFormed s' := h.2.2

theorem finalize_domain_ends_identity (h : RawFinalizeDomain allowed s domain carrier s') :
    domain ∉ s'.liveDomains ∧ Fact.domainLive domain ∉ LiveFacts s' := by
  have dead : domain ∉ s'.liveDomains := by rw [h.post_eq]; simp [finalizeDomainCandidate]
  exact ⟨dead, dead⟩

theorem finalize_domain_consumes_value_carrier (h : RawFinalizeDomain allowed s domain carrier s') :
    s'.domainValueCarrier domain = none := by rw [h.post_eq]; simp [finalizeDomainCandidate]

theorem finalize_domain_preserves_other_domains (h : RawFinalizeDomain allowed s domain carrier s')
    {other : DomainId} (different : other ≠ domain) : other ∈ s'.liveDomains ↔ other ∈ s.liveDomains := by
  rw [h.post_eq]; simp [finalizeDomainCandidate, different]

/-- This milestone allocates no domain identities; finalization only removes one. -/
theorem finalize_domain_liveDomains_subset (h : RawFinalizeDomain allowed s domain carrier s') :
    s'.liveDomains ⊆ s.liveDomains := by
  rw [h.post_eq]; exact Finset.erase_subset _ _

theorem finalize_domain_preserves_other_carriers (h : RawFinalizeDomain allowed s domain carrier s')
    {other : DomainId} (different : other ≠ domain) : s'.domainValueCarrier other = s.domainValueCarrier other := by
  rw [h.post_eq]; simp [finalizeDomainCandidate, different]

theorem finalize_domain_preserves_occupancy (h : RawFinalizeDomain allowed s domain carrier s') :
    s'.occupancy = s.occupancy := by rw [h.post_eq]; rfl

theorem finalize_domain_preserves_packages (h : RawFinalizeDomain allowed s domain carrier s') :
    s'.packages = s.packages ∧ s'.loosePackages = s.loosePackages := by rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem finalize_domain_preserves_histories (h : RawFinalizeDomain allowed s domain carrier s') :
    s'.usedValueFacts = s.usedValueFacts ∧ s'.usedIncarnations = s.usedIncarnations := by
  rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem finalize_domain_preserves_survivors (h : RawFinalizeDomain allowed s domain carrier s') (pkg : PackageId) :
    Survives s' pkg ↔ Survives s pkg := by
  simp only [Survives, IsInstalled, Carries, finalize_domain_preserves_occupancy h,
    (finalize_domain_preserves_packages h).2]

theorem finalize_domain_preserves_carrier_coherence (wf : WellFormed s)
    (h : RawFinalizeDomain allowed s domain carrier s') : DomainCarrierCoherent s' := by
  intro d
  by_cases same : d = domain
  · subst d; rw [h.post_eq]; simp [finalizeDomainCandidate]
  · rw [finalize_domain_preserves_other_domains h same, finalize_domain_preserves_other_carriers h same]
    exact wf.domainCarrierCoherent d

theorem finalize_domain_requires_no_governed_roots (h : FinalizeDomainStep allowed s domain carrier s') :
    ∀ inc, ¬ Governs s inc domain := by
  rintro inc ⟨location, root, live, _, governing⟩
  have post_live : s'.occupancy location = .live root := by
    rw [finalize_domain_preserves_occupancy h.2.1]; exact live
  have domain_live := h.2.2.domainsValid location root post_live
  rw [governing] at domain_live
  exact (finalize_domain_ends_identity h.2.1).1 domain_live

theorem finalize_domain_rejects_live_governed_root {inc : IncarnationId} (governed : Governs s inc domain) :
    ¬ FinalizeDomainStep allowed s domain carrier s' :=
  fun h => finalize_domain_requires_no_governed_roots h inc governed

theorem finalize_domain_requires_no_surviving_domain_dependency
    (h : FinalizeDomainStep allowed s domain carrier s') {pkg : PackageId} {value : ValuePackage}
    (survivor : Survives s pkg) (present : s.packages pkg = some value) :
    Fact.domainLive domain ∉ value.dependencies := by
  intro dep
  have live := h.2.2.dependenciesValid pkg value
    ((finalize_domain_preserves_survivors h.2.1 pkg).mpr survivor)
    ((congrFun (finalize_domain_preserves_packages h.2.1).1 pkg).trans present) _ dep
  exact (finalize_domain_ends_identity h.2.1).2 live

theorem finalize_domain_rejects_surviving_domain_dependency {pkg : PackageId} {value : ValuePackage}
    (survivor : Survives s pkg) (present : s.packages pkg = some value)
    (dep : Fact.domainLive domain ∈ value.dependencies) : ¬ FinalizeDomainStep allowed s domain carrier s' :=
  fun h => finalize_domain_requires_no_surviving_domain_dependency h survivor present dep

theorem finalize_domain_rejects_dead_domain (dead : domain ∉ s.liveDomains) :
    ¬ RawFinalizeDomain allowed s domain carrier s' := by intro h; exact dead h.domain_live

theorem finalize_domain_rejects_missing_permission (missing : ¬ allowed) :
    ¬ RawFinalizeDomain allowed s domain carrier s' := by intro h; exact missing h.finalize_allowed

theorem finalize_domain_rejects_wrong_carrier (wrong : s.domainValueCarrier domain ≠ some carrier) :
    ¬ RawFinalizeDomain allowed s domain carrier s' := by intro h; exact wrong h.current_carrier

theorem finalized_domain_cannot_acquire_ref (h : FinalizeDomainStep allowed s domain carrier s')
    (stable access : Prop) (ptr : PtrToken) : ¬ AcquireRef stable access s' ptr domain :=
  fun acquired => (finalize_domain_ends_identity h.2.1).1 (acquire_ref_implies_live_domain acquired)

end Finalize
end NewLang.F0
