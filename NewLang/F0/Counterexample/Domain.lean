import NewLang.F0.Domain

/-! Concrete domain lifecycle controls and isolated broken rules. -/
namespace NewLang.F0.Counterexample.Domain

private def domain : DomainId := ⟨0⟩
private def otherDomain : DomainId := ⟨1⟩
private def carrierA : DomainValueCarrierId := ⟨0⟩
private def carrierB : DomainValueCarrierId := ⟨1⟩
private def location : RootLocationId := ⟨0⟩
private def rootPkg : PackageId := ⟨0⟩
private def loosePkg : PackageId := ⟨1⟩
private def root : LiveRoot := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, rootPkg, domain⟩
private def ptr : PtrToken := ⟨location, root.incarnation⟩
private def package (dependent : Bool) : ValuePackage :=
  ⟨if dependent then {.domainLive domain} else ∅, true⟩

/-- Multiple domain identities intentionally share one abstract carrier. -/
private def seed (domains : Finset DomainId) : DomainId → Option DomainValueCarrierId :=
  fun d => if d ∈ domains then some carrierA else none

private def snapshot (hasRoot dependent : Bool) (domains : Finset DomainId)
    (carriers : DomainId → Option DomainValueCarrierId) : State where
  occupancy := fun l => if hasRoot then if l = location then .live root else .vacant else .vacant
  packages := fun _ => some (package dependent)
  loosePackages := {loosePkg}
  liveDomains := domains
  domainValueCarrier := carriers
  usedValueFacts := {root.currentFact}
  usedIncarnations := {root.incarnation}

private def before (r d : Bool) : State := snapshot r d {domain, otherDomain} (seed {domain, otherDomain})
private def transferred (r d : Bool) : State := domainTransferCandidate (before r d) domain carrierB
private def finalized (r d : Bool) : State := finalizeDomainCandidate (before r d) domain

private theorem snapshot_live_iff {r d : Bool} {domains : Finset DomainId}
    {carriers : DomainId → Option DomainValueCarrierId} {l : RootLocationId} {actual : LiveRoot} :
    (snapshot r d domains carriers).occupancy l = .live actual ↔
      r = true ∧ l = location ∧ actual = root := by
  cases r <;> by_cases same : l = location <;> simp [snapshot, same, eq_comm]

private theorem snapshot_domains_valid {r d : Bool} {domains : Finset DomainId}
    {carriers : DomainId → Option DomainValueCarrierId} (live : r = true → domain ∈ domains) :
    DomainsValid (snapshot r d domains carriers) := by
  intro l actual current
  rcases snapshot_live_iff.mp current with ⟨yes, _, rfl⟩
  exact live yes

private theorem snapshot_dependencies_valid {r d : Bool} {domains : Finset DomainId}
    {carriers : DomainId → Option DomainValueCarrierId} (live : d = true → domain ∈ domains) :
    DependenciesValid (snapshot r d domains carriers) := by
  intro p value _ defined fact dep
  have same := Option.some.inj defined
  subst value
  by_cases yes : d = true
  · have atom : fact = .domainLive domain := by simpa [package, yes] using dep
    subst fact; exact live yes
  · simp [package, yes] at dep

private theorem snapshot_wellFormed (r d : Bool) (domains : Finset DomainId)
    (carriers : DomainId → Option DomainValueCarrierId)
    (root_live : r = true → domain ∈ domains) (dep_live : d = true → domain ∈ domains)
    (coherent : ∀ dom, dom ∈ domains ↔ ∃ c, carriers dom = some c) :
    WellFormed (snapshot r d domains carriers) := by
  constructor
  · intro p c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;> simp only [Carries, snapshot_live_iff] at h₁ h₂ <;>
      simp_all [snapshot, root, rootPkg, loosePkg]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [snapshot_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [snapshot_live_iff]
  · intro p _; exact ⟨package d, rfl⟩
  · exact snapshot_domains_valid root_live
  · exact snapshot_dependencies_valid dep_live
  · intro l actual current; rcases snapshot_live_iff.mp current with ⟨_, _, rfl⟩
    simp [snapshot]
  · intro l actual current; rcases snapshot_live_iff.mp current with ⟨_, _, rfl⟩
    simp [snapshot]
  · exact coherent

private theorem seed_coherent (domains : Finset DomainId) :
    ∀ d, d ∈ domains ↔ ∃ c, seed domains d = some c := by
  intro d; by_cases live : d ∈ domains <;> simp [seed, live]

private theorem before_wellFormed (r d : Bool) : WellFormed (before r d) :=
  snapshot_wellFormed _ _ _ _ (by simp) (by simp) (seed_coherent _)

private theorem rawTransfer (r d : Bool) :
    RawDomainTransfer True (before r d) domain carrierA carrierB (transferred r d) :=
  ⟨by simp [before, snapshot], by simp [before, snapshot, seed], True.intro, rfl⟩
private theorem transferStep (r d : Bool) :
    DomainTransferStep True (before r d) domain carrierA carrierB (transferred r d) :=
  domain_transfer_step_of_raw (before_wellFormed _ _) (rawTransfer _ _)
private theorem rawFinalize (r d : Bool) :
    RawFinalizeDomain True (before r d) domain carrierA (finalized r d) :=
  ⟨by simp [before, snapshot], by simp [before, snapshot, seed], True.intro, rfl⟩

private theorem governed : Governs (before true false) root.incarnation domain :=
  ⟨location, root, by simp [before, snapshot], rfl, rfl⟩

theorem simple_domain_transfer_is_legal :
    DomainTransferStep True (before false false) domain carrierA carrierB (transferred false false) ∧
    carrierA ≠ carrierB ∧ (transferred false false).domainValueCarrier domain = some carrierB :=
  ⟨transferStep _ _, by decide, (domain_transfer_moves_value_carrier (rawTransfer _ _)).2⟩

theorem governed_root_allows_transfer_but_rejects_finalization :
    WellFormed (before true false) ∧ Governs (before true false) root.incarnation domain ∧
    DomainTransferStep True (before true false) domain carrierA carrierB (transferred true false) ∧
    Governs (transferred true false) root.incarnation domain ∧
    ∀ candidate, ¬ FinalizeDomainStep True (before true false) domain carrierA candidate :=
  ⟨before_wellFormed _ _, governed, transferStep _ _,
   (domain_transfer_preserves_governing_relations (rawTransfer _ _) _ _).mpr governed,
   fun _ => finalize_domain_rejects_live_governed_root governed⟩

theorem DomainLive_dependency_allows_transfer_but_rejects_finalization :
    WellFormed (before false true) ∧ Survives (before false true) loosePkg ∧
    Fact.domainLive domain ∈ (package true).dependencies ∧
    DomainTransferStep True (before false true) domain carrierA carrierB (transferred false true) ∧
    Fact.domainLive domain ∈ LiveFacts (transferred false true) ∧
    ∀ candidate, ¬ FinalizeDomainStep True (before false true) domain carrierA candidate := by
  have survivor : Survives (before false true) loosePkg := Or.inr (by simp [before, snapshot])
  have dep : Fact.domainLive domain ∈ (package true).dependencies := by simp [package]
  refine ⟨before_wellFormed _ _, survivor, dep, transferStep _ _, ?_, ?_⟩
  · exact (domain_transfer_preserves_DomainLive_dependencies (transferStep _ _) survivor rfl dep).2.2
  · intro candidate; exact finalize_domain_rejects_surviving_domain_dependency survivor rfl dep

private theorem finalized_wellFormed : WellFormed (finalized false false) := by
  have wf := before_wellFormed false false
  refine ⟨wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique, wf.packagesPresent,
    ?_, ?_, wf.valueFactsRecorded, wf.incarnationsRecorded,
    finalize_domain_preserves_carrier_coherence wf (rawFinalize _ _)⟩
  · exact snapshot_domains_valid (r := false) (d := false) (by simp)
  · exact snapshot_dependencies_valid (r := false) (d := false) (by simp)
private theorem finalizeStep :
    FinalizeDomainStep True (before false false) domain carrierA (finalized false false) :=
  ⟨before_wellFormed _ _, rawFinalize _ _, finalized_wellFormed⟩

theorem independent_domain_finalization_is_legal :
    FinalizeDomainStep True (before false false) domain carrierA (finalized false false) ∧
    domain ∉ (finalized false false).liveDomains ∧
    Fact.domainLive domain ∉ LiveFacts (finalized false false) ∧
    (finalized false false).domainValueCarrier domain = none ∧
    otherDomain ∈ (finalized false false).liveDomains ∧
    (finalized false false).domainValueCarrier otherDomain = some carrierA :=
  ⟨finalizeStep, (finalize_domain_ends_identity (rawFinalize _ _)).1,
   (finalize_domain_ends_identity (rawFinalize _ _)).2,
   finalize_domain_consumes_value_carrier (rawFinalize _ _),
   (finalize_domain_preserves_other_domains (rawFinalize _ _) (by decide)).mpr (by simp [before, snapshot]),
   (finalize_domain_preserves_other_carriers (rawFinalize _ _) (by decide)).trans (by simp [before, snapshot, seed])⟩

theorem one_carrier_may_hold_multiple_domain_identities :
    WellFormed (before false false) ∧ domain ≠ otherDomain ∧
    (before false false).domainValueCarrier domain = some carrierA ∧
    (before false false).domainValueCarrier otherDomain = some carrierA :=
  ⟨before_wellFormed _ _, by decide, by simp [before, snapshot, seed], by simp [before, snapshot, seed]⟩

theorem transfer_with_root_and_dependency_preserves_acquisition :
    DomainTransferStep True (before true true) domain carrierA carrierB (transferred true true) ∧
    AcquireRef True True (before true true) ptr domain ∧
    AcquireRef True True (transferred true true) ptr domain ∧
    Governs (transferred true true) ptr.incarnation domain ∧
    Fact.domainLive domain ∈ LiveFacts (transferred true true) := by
  have acquired : AcquireRef True True (before true true) ptr domain :=
    ⟨before_wellFormed _ _, ⟨⟨root, by simp [before, snapshot, ptr], rfl, rfl⟩, True.intro, True.intro⟩⟩
  have after := domain_transfer_preserves_acquire_ref (transferStep true true) acquired True.intro True.intro
  exact ⟨transferStep _ _, acquired, after, acquire_ref_implies_governing_relation after,
    acquire_ref_implies_live_domain after⟩

/-- Raw end clears only the domain/carrier; the governed root is left in place. -/
theorem unchecked_finalization_strands_governed_root_only :
    WellFormed (before true false) ∧ RawFinalizeDomain True (before true false) domain carrierA (finalized true false) ∧
    CarrierUnique (finalized true false) ∧ PlacesUnique (finalized true false) ∧
    IncarnationsUnique (finalized true false) ∧ PackagesPresent (finalized true false) ∧
    DependenciesValid (finalized true false) ∧ ValueFactsRecorded (finalized true false) ∧
    IncarnationsRecorded (finalized true false) ∧ DomainCarrierCoherent (finalized true false) ∧
    ¬ DomainsValid (finalized true false) := by
  have wf := before_wellFormed true false
  refine ⟨wf, rawFinalize _ _, wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique,
    wf.packagesPresent, ?_, wf.valueFactsRecorded, wf.incarnationsRecorded,
    finalize_domain_preserves_carrier_coherence wf (rawFinalize _ _), ?_⟩
  · exact snapshot_dependencies_valid (r := true) (d := false) (by simp)
  · intro valid
    exact (finalize_domain_ends_identity (rawFinalize true false)).1
      (valid location root (by simp [finalized, finalizeDomainCandidate, before, snapshot]))

theorem unchecked_finalization_strands_domain_dependency_only :
    WellFormed (before false true) ∧ RawFinalizeDomain True (before false true) domain carrierA (finalized false true) ∧
    CarrierUnique (finalized false true) ∧ PlacesUnique (finalized false true) ∧
    IncarnationsUnique (finalized false true) ∧ PackagesPresent (finalized false true) ∧
    DomainsValid (finalized false true) ∧ ValueFactsRecorded (finalized false true) ∧
    IncarnationsRecorded (finalized false true) ∧ DomainCarrierCoherent (finalized false true) ∧
    ¬ DependenciesValid (finalized false true) := by
  have wf := before_wellFormed false true
  refine ⟨wf, rawFinalize _ _, wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique,
    wf.packagesPresent, ?_, wf.valueFactsRecorded, wf.incarnationsRecorded,
    finalize_domain_preserves_carrier_coherence wf (rawFinalize _ _), ?_⟩
  · exact snapshot_domains_valid (r := false) (d := true) (by simp)
  · intro valid
    have live := valid loosePkg (package true) (Or.inr (by simp [finalized, finalizeDomainCandidate, before, snapshot]))
      rfl (.domainLive domain) (by simp [package])
    exact (finalize_domain_ends_identity (rawFinalize false true)).2 live

private def ended : State := destroyCandidate (before true false) location root
private theorem ended_eq : ended = before false false := by
  simp [ended, destroyCandidate, before, snapshot, root, rootPkg, loosePkg]
  funext l; by_cases same : l = location <;> simp [same]
private theorem destroyStep : DestroyStep True (before true false) location root domain ended :=
  ⟨before_wellFormed _ _, ⟨by simp [before, snapshot], rfl, True.intro, ⟨package false, rfl, rfl⟩, rfl⟩,
   by rw [ended_eq]; exact before_wellFormed _ _⟩

theorem ending_root_allows_later_domain_finalization :
    (∀ candidate, ¬ FinalizeDomainStep True (before true false) domain carrierA candidate) ∧
    DestroyStep True (before true false) location root domain ended ∧
    domain ∈ ended.liveDomains ∧ ended.domainValueCarrier domain = some carrierA ∧
    ¬ LiveIncarnation ended root.incarnation ∧
    FinalizeDomainStep True ended domain carrierA (finalized false false) := by
  refine ⟨fun _ => finalize_domain_rejects_live_governed_root governed, destroyStep, ?_, ?_,
    destroy_ends_incarnation destroyStep.1 destroyStep.2.1, ?_⟩
  · exact destroy_does_not_finalize_domain destroyStep.1 destroyStep.2.1
  · rw [destroy_preserves_domain_carriers destroyStep.2.1]; simp [before, snapshot, seed]
  · rw [ended_eq]; exact finalizeStep

private def renamedBefore : State := snapshot false false {domain} (seed {domain})
/-- Deliberately wrong identity replacement; other state is unchanged. -/
private def TransferRenamingIdentity (s : State) : State :=
  {s with
    liveDomains := insert otherDomain (s.liveDomains.erase domain)
    domainValueCarrier := fun d => if d = otherDomain then s.domainValueCarrier domain
      else if d = domain then none else s.domainValueCarrier d}
private def renamedAfter : State := TransferRenamingIdentity renamedBefore
private theorem renamedAfter_eq : renamedAfter = snapshot false false {otherDomain} (seed {otherDomain}) := by
  simp [renamedAfter, TransferRenamingIdentity, renamedBefore, snapshot, seed]
  funext d
  by_cases is_old : d = domain
  · subst d; simp [seed, domain, otherDomain]
  · by_cases is_new : d = otherDomain <;> simp [seed, is_old, is_new]

theorem broken_identity_rename_can_preserve_wellFormed :
    WellFormed renamedBefore ∧ WellFormed renamedAfter ∧
    domain ∈ renamedBefore.liveDomains ∧ domain ∉ renamedAfter.liveDomains ∧
    otherDomain ∉ renamedBefore.liveDomains ∧ otherDomain ∈ renamedAfter.liveDomains ∧
    renamedBefore.domainValueCarrier domain = some carrierA ∧
    renamedAfter.domainValueCarrier otherDomain = some carrierA ∧
    ¬ DomainTransferStep True renamedBefore domain carrierA carrierB renamedAfter := by
  have pre := snapshot_wellFormed false false {domain} (seed {domain}) (by simp) (by simp) (seed_coherent _)
  have post : WellFormed renamedAfter := by
    rw [renamedAfter_eq]; exact snapshot_wellFormed _ _ _ _ (by simp) (by simp) (seed_coherent _)
  refine ⟨pre, post, by simp [renamedBefore, snapshot], ?_, ?_, ?_,
    by simp [renamedBefore, snapshot, seed], ?_, ?_⟩
  · rw [renamedAfter_eq]; simp [snapshot, domain, otherDomain]
  · simp [renamedBefore, snapshot, domain, otherDomain]
  · rw [renamedAfter_eq]; simp [snapshot]
  · rw [renamedAfter_eq]; simp [snapshot, seed]
  · intro legal
    have old_live := (domain_transfer_preserves_liveness legal.2.1).2
    rw [renamedAfter_eq] at old_live
    simp [snapshot, domain, otherDomain] at old_live

theorem missing_permissions_and_wrong_carriers_are_rejected (candidate : State) :
    ¬ RawDomainTransfer False (before false false) domain carrierA carrierB candidate ∧
    ¬ RawFinalizeDomain False (before false false) domain carrierA candidate ∧
    ¬ RawDomainTransfer True (before false false) domain carrierB carrierA candidate ∧
    ¬ RawFinalizeDomain True (before false false) domain carrierB candidate :=
  ⟨domain_transfer_rejects_missing_permission not_false, finalize_domain_rejects_missing_permission not_false,
   domain_transfer_rejects_wrong_carrier (by simp [before, snapshot, seed, carrierA, carrierB]),
   finalize_domain_rejects_wrong_carrier (by simp [before, snapshot, seed, carrierA, carrierB])⟩

theorem dead_domain_cannot_transfer_or_be_finalized_again (candidate : State) :
    ¬ RawDomainTransfer True (finalized false false) domain carrierA carrierB candidate ∧
    ¬ RawFinalizeDomain True (finalized false false) domain carrierA candidate :=
  ⟨domain_transfer_rejects_dead_domain (finalize_domain_ends_identity (rawFinalize _ _)).1,
   finalize_domain_rejects_dead_domain (finalize_domain_ends_identity (rawFinalize _ _)).1⟩

end NewLang.F0.Counterexample.Domain
