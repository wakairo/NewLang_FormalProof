import NewLang.F0.Lifetime
import NewLang.F0.Replace

namespace NewLang.F0

/-- Persistent external mathematical value; neither a current-value version nor a ref.
Construction of a Lean value alone does not establish source-level safe issuance. -/
structure PtrToken where
  location : RootLocationId
  incarnation : IncarnationId
  deriving DecidableEq, Repr

/-- Point-of-acquisition obligation at the exact token location. -/
def CurrentPtr (s : State) (ptr : PtrToken) : Prop :=
  ∃ root, s.occupancy ptr.location = .live root ∧ root.incarnation = ptr.incarnation

/-- Raw acquisition is a derivation, not a state transition or a persistent ref result.
The two propositions stand for ordinary domain stability evidence and all omitted
access/provenance/representation/backing obligations. Neither is universally true. -/
structure RawAcquireRef (hasStableEvidence canAccess : Prop)
    (s : State) (ptr : PtrToken) (evidenceDomain : DomainId) : Prop where
  target : ∃ root, s.occupancy ptr.location = .live root ∧
    root.incarnation = ptr.incarnation ∧ root.governing = evidenceDomain
  stability : hasStableEvidence
  access : canAccess

/-- F0.5 checks current acquisition legality only; lexical use scopes are deferred. -/
def AcquireRef (hasStableEvidence canAccess : Prop)
    (s : State) (ptr : PtrToken) (evidenceDomain : DomainId) : Prop :=
  WellFormed s ∧ RawAcquireRef hasStableEvidence canAccess s ptr evidenceDomain

/-- Encoding of initialize's result. The issuance theorem, not this pure constructor,
connects the value to a successful safe lifetime start. -/
def ptrFromInitialize (location : RootLocationId) (incarnation : IncarnationId) : PtrToken :=
  ⟨location, incarnation⟩

section Acquire
variable {stable access : Prop} {s : State} {ptr : PtrToken} {domain : DomainId}

theorem acquire_ref_targets_exact_location_incarnation
    (h : AcquireRef stable access s ptr domain) : CurrentPtr s ptr := by
  rcases h.2.target with ⟨root, live, incarnation, _⟩
  exact ⟨root, live, incarnation⟩

theorem acquire_ref_implies_live_incarnation
    (h : AcquireRef stable access s ptr domain) : LiveIncarnation s ptr.incarnation := by
  rcases acquire_ref_targets_exact_location_incarnation h with ⟨root, live, incarnation⟩
  exact ⟨ptr.location, root, live, incarnation⟩

theorem acquire_ref_matches_governing_domain (h : AcquireRef stable access s ptr domain) :
    ∃ root, s.occupancy ptr.location = .live root ∧
      root.incarnation = ptr.incarnation ∧ root.governing = domain := h.2.target

theorem acquire_ref_implies_governing_relation (h : AcquireRef stable access s ptr domain) :
    Governs s ptr.incarnation domain := by
  rcases h.2.target with ⟨root, live, incarnation, governing⟩
  exact ⟨ptr.location, root, live, incarnation, governing⟩

theorem acquire_ref_implies_live_domain (h : AcquireRef stable access s ptr domain) :
    domain ∈ s.liveDomains := by
  rcases h.2.target with ⟨root, live, _, governing⟩
  rw [← governing]; exact h.1.domainsValid ptr.location root live

theorem acquire_ref_rejects_missing_stability_evidence (missing : ¬ stable) :
    ¬ AcquireRef stable access s ptr domain := by intro h; exact missing h.2.stability

theorem acquire_ref_rejects_missing_access_or_provenance_premise (missing : ¬ access) :
    ¬ AcquireRef stable access s ptr domain := by intro h; exact missing h.2.access

theorem acquire_ref_rejects_wrong_domain {root : LiveRoot}
    (live : s.occupancy ptr.location = .live root) (wrong : domain ≠ root.governing) :
    ¬ AcquireRef stable access s ptr domain := by
  intro h
  rcases h.2.target with ⟨actual, actual_live, _, governing⟩
  have same := Occupancy.live.inj (live.symm.trans actual_live)
  exact wrong (governing.symm.trans (congrArg LiveRoot.governing same).symm)

theorem acquire_ref_rejects_incarnation_mismatch {root : LiveRoot}
    (live : s.occupancy ptr.location = .live root) (wrong : ptr.incarnation ≠ root.incarnation) :
    ¬ AcquireRef stable access s ptr domain := by
  intro h
  rcases h.2.target with ⟨actual, actual_live, incarnation, _⟩
  have same := Occupancy.live.inj (live.symm.trans actual_live)
  exact wrong (incarnation.symm.trans (congrArg LiveRoot.incarnation same).symm)

theorem ended_incarnation_cannot_acquire_ref (ended : ¬ LiveIncarnation s ptr.incarnation) :
    ¬ AcquireRef stable access s ptr domain :=
  fun h => ended (acquire_ref_implies_live_incarnation h)

end Acquire

section Initialize
variable {sites : RootSiteLayout} {ci tc stable access : Prop} {s s' : State}
  {location : RootLocationId} {pkg : PackageId} {domain : DomainId}
  {incarnation : IncarnationId} {fact : ValueFactId}

theorem initialize_yields_current_ptr
    (h : InitializeStep sites ci tc s location pkg domain incarnation fact s') :
    let ptr := ptrFromInitialize location incarnation
    ptr.location = location ∧ ptr.incarnation = incarnation ∧
      FreshIncarnation s ptr.incarnation ∧ CurrentPtr s' ptr :=
  ⟨rfl, rfl, h.2.1.fresh_incarnation, _, h.2.1.target_after, rfl⟩

theorem initialize_ptr_can_acquire_ref
    (h : InitializeStep sites ci tc s location pkg domain incarnation fact s')
    (evidence : stable) (allowed : access) :
    AcquireRef stable access s' (ptrFromInitialize location incarnation) domain :=
  ⟨h.2.2, ⟨⟨_, h.2.1.target_after, rfl, rfl⟩, evidence, allowed⟩⟩

/-- Retained history and exact identity checking prevent revival even though this site
is live again. Both old/new starts in a lifecycle must use the same fixed layout. -/
theorem reinitialize_does_not_revive_old_ptr {ptr : PtrToken}
    (h : RawInitialize sites ci tc s location pkg domain incarnation fact s')
    (same_site : ptr.location = location) (used : ptr.incarnation ∈ s.usedIncarnations)
    (evidenceDomain : DomainId) : ¬ AcquireRef stable access s' ptr evidenceDomain := by
  apply acquire_ref_rejects_incarnation_mismatch
    (root := initializeRoot sites location pkg domain incarnation fact)
  · rw [same_site]; exact h.target_after
  · intro same
    apply h.fresh_incarnation
    simpa [initializeRoot, same] using used

end Initialize

section End
variable {ce stable access : Prop} {s s' : State} {location : RootLocationId}
  {root : LiveRoot} {endingDomain evidenceDomain : DomainId} {ptr : PtrToken}

theorem stale_ptr_after_take_cannot_acquire_ref (wf : WellFormed s)
    (h : RawTake ce s location root endingDomain s') (points_to_old : ptr.incarnation = root.incarnation) :
    ¬ AcquireRef stable access s' ptr evidenceDomain := by
  apply ended_incarnation_cannot_acquire_ref
  rw [points_to_old]; exact take_ends_incarnation wf h

theorem stale_ptr_after_destroy_cannot_acquire_ref (wf : WellFormed s)
    (h : RawDestroy ce s location root endingDomain s') (points_to_old : ptr.incarnation = root.incarnation) :
    ¬ AcquireRef stable access s' ptr evidenceDomain := by
  apply ended_incarnation_cannot_acquire_ref
  rw [points_to_old]; exact destroy_ends_incarnation wf h

theorem take_then_reinitialize_does_not_revive_old_ptr
    {sites : RootSiteLayout} {ci tc : Prop} {final : State} {pkg : PackageId}
    {domain : DomainId} {incarnation : IncarnationId} {fact : ValueFactId}
    (wf : WellFormed s) (ended : RawTake ce s location root endingDomain s')
    (started : RawInitialize sites ci tc s' location pkg domain incarnation fact final) :
    ¬ AcquireRef stable access final (ptrFromInitialize location root.incarnation) evidenceDomain :=
  reinitialize_does_not_revive_old_ptr started rfl (take_ended_identities_remain_recorded wf ended).1 _

theorem destroy_then_reinitialize_does_not_revive_old_ptr
    {sites : RootSiteLayout} {ci tc : Prop} {final : State} {pkg : PackageId}
    {domain : DomainId} {incarnation : IncarnationId} {fact : ValueFactId}
    (wf : WellFormed s) (ended : RawDestroy ce s location root endingDomain s')
    (started : RawInitialize sites ci tc s' location pkg domain incarnation fact final) :
    ¬ AcquireRef stable access final (ptrFromInitialize location root.incarnation) evidenceDomain :=
  reinitialize_does_not_revive_old_ptr started rfl (destroy_ended_identities_remain_recorded wf ended).1 _

end End

/-- Current value changes do not change pointer identity. All omitted access obligations
must be supplied for the new state; this does not assert future-use ref stability. -/
theorem ptr_remains_live_across_current_value_replace
    {cw tc stable access : Prop} {s s' : State} {location : RootLocationId}
    {root : LiveRoot} {incoming : PackageId} {fact : ValueFactId} {ptr : PtrToken}
    {domain : DomainId} (h : ReplaceStep cw tc s location root incoming fact s')
    (same_site : ptr.location = location) (incarnation : root.incarnation = ptr.incarnation)
    (governing : root.governing = domain) (evidence : stable) (allowed : access) :
    AcquireRef stable access s' ptr domain := by
  refine ⟨h.2.2, ⟨⟨{root with currentFact := fact, package := incoming},
    ?_, incarnation, governing⟩, evidence, allowed⟩⟩
  rw [same_site]; exact h.2.1.target_after

end NewLang.F0
