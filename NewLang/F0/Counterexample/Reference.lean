import NewLang.F0.Reference

/-! Concrete acquisition controls and private omitted-guard countermodels. -/
namespace NewLang.F0.Counterexample.Reference

private def location : RootLocationId := ⟨0⟩
private def pkgA : PackageId := ⟨0⟩
private def pkgB : PackageId := ⟨1⟩
private def domain : DomainId := ⟨0⟩
private def wrongDomain : DomainId := ⟨1⟩
private def sites : RootSiteLayout where
  placeAt := fun l => ⟨l.index⟩
  injective := by intro a b same; cases a; cases b; cases same; rfl
private def package : ValuePackage := ⟨∅, true⟩
private def root (pkg : PackageId) (inc fact : Nat) : LiveRoot :=
  initializeRoot sites location pkg domain ⟨inc⟩ ⟨fact⟩

/-- Uncarried entries are inert. A constant table keeps the concrete fixture small. -/
private def fixture (occupant : Option LiveRoot) (loose : Finset PackageId)
    (incarnations : Finset IncarnationId) (facts : Finset ValueFactId) : State where
  occupancy := fun l => if l = location then
    match occupant with | none => .vacant | some r => .live r
    else .vacant
  packages := fun _ => some package
  loosePackages := loose
  liveDomains := {domain, wrongDomain}
  domainValueCarrier := fun d => if d ∈ ({domain, wrongDomain} : Finset DomainId) then some ⟨d.index⟩ else none
  usedIncarnations := incarnations
  usedValueFacts := facts

private theorem fixture_live_iff {r actual : LiveRoot} {l : RootLocationId}
    {loose : Finset PackageId} {incs : Finset IncarnationId} {facts : Finset ValueFactId} :
    (fixture (some r) loose incs facts).occupancy l = .live actual ↔ l = location ∧ actual = r := by
  by_cases same : l = location <;> simp [fixture, same, eq_comm]

private theorem fixture_dependencies_valid (occupant : Option LiveRoot) (loose : Finset PackageId)
    (incs : Finset IncarnationId) (facts : Finset ValueFactId) :
    DependenciesValid (fixture occupant loose incs facts) := by
  intro p value _ defined fact dependency
  have same : package = value := Option.some.inj defined
  subst value; simp [package] at dependency

private theorem vacant_wellFormed (loose : Finset PackageId) (incs : Finset IncarnationId)
    (facts : Finset ValueFactId) : WellFormed (fixture none loose incs facts) := by
  constructor
  · intro p c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;> simp_all [Carries, fixture]
  · simp [PlacesUnique, fixture]
  · simp [IncarnationsUnique, fixture]
  · intro p _; exact ⟨package, rfl⟩
  · simp [DomainsValid, fixture]
  · exact fixture_dependencies_valid _ _ _ _
  · simp [ValueFactsRecorded, fixture]
  · simp [IncarnationsRecorded, fixture]
  · intro dom
    simp only [fixture]
    split <;> simp_all

private theorem live_wellFormed (pkg : PackageId) (inc fact : Nat) (loose : Finset PackageId)
    (incs : Finset IncarnationId) (facts : Finset ValueFactId)
    (not_loose : pkg ∉ loose) (inc_recorded : (⟨inc⟩ : IncarnationId) ∈ incs)
    (fact_recorded : (⟨fact⟩ : ValueFactId) ∈ facts) :
    WellFormed (fixture (some (root pkg inc fact)) loose incs facts) := by
  constructor
  · intro p c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;> simp only [Carries, fixture_live_iff] at h₁ h₂ <;>
      simp_all [fixture, root, initializeRoot]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [fixture_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [fixture_live_iff]
  · intro p _; exact ⟨package, rfl⟩
  · intro l r live; rcases fixture_live_iff.mp live with ⟨_, rfl⟩
    simp [fixture, root, initializeRoot]
  · exact fixture_dependencies_valid _ _ _ _
  · intro l r live; rcases fixture_live_iff.mp live with ⟨_, rfl⟩; exact fact_recorded
  · intro l r live; rcases fixture_live_iff.mp live with ⟨_, rfl⟩; exact inc_recorded
  · intro dom
    simp only [fixture]
    split <;> simp_all

private def start : State := fixture none {pkgA, pkgB} ∅ ∅
private def first : State := initializeCandidate sites start location pkgA domain ⟨1⟩ ⟨1⟩
private def taken : State := takeCandidate first location (root pkgA 1 1)
private def destroyed : State := destroyCandidate first location (root pkgA 1 1)
private def restarted (ended : State) : State :=
  initializeCandidate sites ended location pkgB domain ⟨2⟩ ⟨2⟩
private def oldPtr : PtrToken := ptrFromInitialize location ⟨1⟩
private def newPtr : PtrToken := ptrFromInitialize location ⟨2⟩

private theorem first_eq : first = fixture (some (root pkgA 1 1)) {pkgB} {⟨1⟩} {⟨1⟩} := by
  simp [first, initializeCandidate, start, fixture, root, pkgA, pkgB]
private theorem taken_eq : taken = fixture none {pkgA, pkgB} {⟨1⟩} {⟨1⟩} := by
  simp [taken, takeCandidate, first_eq, fixture, root, initializeRoot]
  funext l; by_cases same : l = location <;> simp [same]
private theorem destroyed_eq : destroyed = fixture none {pkgB} {⟨1⟩} {⟨1⟩} := by
  simp [destroyed, destroyCandidate, first_eq, fixture, root, initializeRoot, pkgA, pkgB]
  funext l; by_cases same : l = location <;> simp [same]
private theorem restarted_taken_eq : restarted taken =
    fixture (some (root pkgB 2 2)) {pkgA} {⟨2⟩, ⟨1⟩} {⟨2⟩, ⟨1⟩} := by
  simp [restarted, initializeCandidate, taken_eq, fixture, root, pkgA, pkgB]
  decide
private theorem restarted_destroyed_eq : restarted destroyed =
    fixture (some (root pkgB 2 2)) ∅ {⟨2⟩, ⟨1⟩} {⟨2⟩, ⟨1⟩} := by
  simp [restarted, initializeCandidate, destroyed_eq, fixture, root]

private theorem initializeFirst :
    InitializeStep sites True True start location pkgA domain ⟨1⟩ ⟨1⟩ first := by
  refine ⟨vacant_wellFormed _ _ _, ?_, ?_⟩
  · refine ⟨by simp [start, fixture], by simp [start, fixture], by simp [start, fixture],
      by simp [FreshIncarnation, start, fixture], by simp [FreshValueFact, start, fixture],
      True.intro, True.intro, rfl⟩
  · rw [first_eq]; exact live_wellFormed _ _ _ _ _ _ (by decide) (by simp) (by simp)

private theorem takeFirst : TakeStep True first location (root pkgA 1 1) domain taken := by
  refine ⟨initializeFirst.2.2, ⟨initializeFirst.2.1.target_after, rfl, True.intro, rfl⟩, ?_⟩
  rw [taken_eq]; exact vacant_wellFormed _ _ _
private theorem destroyFirst : DestroyStep True first location (root pkgA 1 1) domain destroyed := by
  refine ⟨initializeFirst.2.2, ⟨initializeFirst.2.1.target_after, rfl, True.intro,
    ⟨package, rfl, rfl⟩, rfl⟩, ?_⟩
  rw [destroyed_eq]; exact vacant_wellFormed _ _ _

private theorem reinitializeTaken :
    InitializeStep sites True True taken location pkgB domain ⟨2⟩ ⟨2⟩ (restarted taken) := by
  refine ⟨takeFirst.2.2, ?_, ?_⟩
  · refine ⟨take_restores_vacancy takeFirst.2.1, ?_, ?_, ?_, ?_, True.intro, True.intro, rfl⟩ <;>
      simp [taken_eq, fixture, FreshIncarnation, FreshValueFact]
  · rw [restarted_taken_eq]; exact live_wellFormed _ _ _ _ _ _ (by decide) (by simp) (by simp)
private theorem reinitializeDestroyed :
    InitializeStep sites True True destroyed location pkgB domain ⟨2⟩ ⟨2⟩ (restarted destroyed) := by
  refine ⟨destroyFirst.2.2, ?_, ?_⟩
  · refine ⟨destroy_restores_vacancy destroyFirst.2.1, ?_, ?_, ?_, ?_, True.intro, True.intro, rfl⟩ <;>
      simp [destroyed_eq, fixture, FreshIncarnation, FreshValueFact]
  · rw [restarted_destroyed_eq]; exact live_wellFormed _ _ _ _ _ _ (by simp) (by simp) (by simp)

private theorem acquireFirst : AcquireRef True True first oldPtr domain :=
  initialize_ptr_can_acquire_ref initializeFirst True.intro True.intro

theorem initialized_ptr_is_safely_issued_and_acquires_ref :
    InitializeStep sites True True start location pkgA domain ⟨1⟩ ⟨1⟩ first ∧
    oldPtr.location = location ∧ oldPtr.incarnation = ⟨1⟩ ∧ CurrentPtr first oldPtr ∧
    AcquireRef True True first oldPtr domain :=
  ⟨initializeFirst, rfl, rfl, (initialize_yields_current_ptr initializeFirst).2.2.2,
   acquireFirst⟩

theorem take_stale_ptr_contrast :
    AcquireRef True True first oldPtr domain ∧
    TakeStep True first location (root pkgA 1 1) domain taken ∧
    oldPtr.location = location ∧ oldPtr.incarnation = ⟨1⟩ ∧
    ¬ AcquireRef True True taken oldPtr domain :=
  ⟨acquireFirst, takeFirst, rfl, rfl,
   stale_ptr_after_take_cannot_acquire_ref takeFirst.1 takeFirst.2.1 rfl⟩

theorem destroy_stale_ptr_contrast :
    AcquireRef True True first oldPtr domain ∧
    DestroyStep True first location (root pkgA 1 1) domain destroyed ∧
    oldPtr.location = location ∧ oldPtr.incarnation = ⟨1⟩ ∧
    ¬ AcquireRef True True destroyed oldPtr domain :=
  ⟨acquireFirst, destroyFirst, rfl, rfl,
   stale_ptr_after_destroy_cannot_acquire_ref destroyFirst.1 destroyFirst.2.1 rfl⟩

/-- Both starts share exactly the same layout and site; location is live again. -/
theorem same_site_reinitialize_old_ptr_rejected_new_ptr_accepted :
    InitializeStep sites True True start location pkgA domain ⟨1⟩ ⟨1⟩ first ∧
    TakeStep True first location (root pkgA 1 1) domain taken ∧
    InitializeStep sites True True taken location pkgB domain ⟨2⟩ ⟨2⟩ (restarted taken) ∧
    (restarted taken).occupancy location = .live (root pkgB 2 2) ∧
    (root pkgB 2 2).place = (root pkgA 1 1).place ∧ oldPtr.location = newPtr.location ∧
    oldPtr.incarnation ≠ newPtr.incarnation ∧
    ¬ AcquireRef True True (restarted taken) oldPtr domain ∧
    AcquireRef True True (restarted taken) newPtr domain :=
  ⟨initializeFirst, takeFirst, reinitializeTaken, reinitializeTaken.2.1.target_after, rfl, rfl,
   by decide, take_then_reinitialize_does_not_revive_old_ptr takeFirst.1 takeFirst.2.1
     reinitializeTaken.2.1, initialize_ptr_can_acquire_ref reinitializeTaken True.intro True.intro⟩

theorem same_site_destroy_reinitialize_old_ptr_rejected_new_ptr_accepted :
    InitializeStep sites True True start location pkgA domain ⟨1⟩ ⟨1⟩ first ∧
    DestroyStep True first location (root pkgA 1 1) domain destroyed ∧
    InitializeStep sites True True destroyed location pkgB domain ⟨2⟩ ⟨2⟩ (restarted destroyed) ∧
    (restarted destroyed).occupancy location = .live (root pkgB 2 2) ∧
    (root pkgB 2 2).place = (root pkgA 1 1).place ∧
    ¬ AcquireRef True True (restarted destroyed) oldPtr domain ∧
    AcquireRef True True (restarted destroyed) newPtr domain :=
  ⟨initializeFirst, destroyFirst, reinitializeDestroyed, reinitializeDestroyed.2.1.target_after, rfl,
   destroy_then_reinitialize_does_not_revive_old_ptr destroyFirst.1 destroyFirst.2.1
     reinitializeDestroyed.2.1, initialize_ptr_can_acquire_ref reinitializeDestroyed True.intro True.intro⟩

theorem missing_stability_wrong_domain_and_missing_access_are_rejected :
    domain ∈ first.liveDomains ∧ wrongDomain ∈ first.liveDomains ∧ CurrentPtr first oldPtr ∧
    ¬ AcquireRef False True first oldPtr domain ∧
    ¬ AcquireRef True True first oldPtr wrongDomain ∧
    ¬ AcquireRef True False first oldPtr domain :=
  ⟨by simp [first_eq, fixture], by simp [first_eq, fixture],
   (initialize_yields_current_ptr initializeFirst).2.2.2,
   acquire_ref_rejects_missing_stability_evidence not_false,
   acquire_ref_rejects_wrong_domain initializeFirst.2.1.target_after (by decide),
   acquire_ref_rejects_missing_access_or_provenance_premise not_false⟩

private def replaced : State := replaceCandidate first location (root pkgA 1 1) pkgB ⟨2⟩
private theorem replaced_eq : replaced =
    fixture (some (root pkgB 1 2)) {pkgA} {⟨1⟩} {⟨2⟩, ⟨1⟩} := by
  simp [replaced, replaceCandidate, first_eq, fixture, root, initializeRoot, pkgA, pkgB]
  funext l; by_cases same : l = location <;> simp [same]
private theorem replaceFirst : ReplaceStep True True first location (root pkgA 1 1) pkgB ⟨2⟩ replaced := by
  refine ⟨initializeFirst.2.2, ⟨initializeFirst.2.1.target_after, ?_, ?_, True.intro, True.intro, rfl⟩, ?_⟩
  · simp [first_eq, fixture]
  · simp [FreshValueFact, first_eq, fixture]
  · rw [replaced_eq]; exact live_wellFormed _ _ _ _ _ _ (by decide) (by simp) (by simp)

theorem replace_changes_current_fact_but_same_ptr_acquires_ref :
    AcquireRef True True first oldPtr domain ∧
    ReplaceStep True True first location (root pkgA 1 1) pkgB ⟨2⟩ replaced ∧
    replaced.occupancy location = .live (root pkgB 1 2) ∧
    (root pkgB 1 2).currentFact ≠ (root pkgA 1 1).currentFact ∧
    (root pkgB 1 2).incarnation = oldPtr.incarnation ∧ AcquireRef True True replaced oldPtr domain :=
  ⟨acquireFirst, replaceFirst, replaceFirst.2.1.target_after,
   by decide, rfl, ptr_remains_live_across_current_value_replace replaceFirst rfl rfl rfl True.intro True.intro⟩

/-- Exactly RawInitialize's obligations except incarnation freshness. -/
private def InitializeIgnoringIncarnationFreshness (ci tc : Prop) (s : State)
    (inc : IncarnationId) (fact : ValueFactId) (s' : State) : Prop :=
  s.occupancy location = .vacant ∧ pkgB ∈ s.loosePackages ∧ domain ∈ s.liveDomains ∧
  FreshValueFact s fact ∧ ci ∧ tc ∧
  s' = initializeCandidate sites s location pkgB domain inc fact
private def revived : State := initializeCandidate sites taken location pkgB domain ⟨1⟩ ⟨2⟩
private theorem revived_eq : revived =
    fixture (some (root pkgB 1 2)) {pkgA} {⟨1⟩} {⟨2⟩, ⟨1⟩} := by
  simp [revived, initializeCandidate, taken_eq, fixture, root, pkgA, pkgB]
  decide

theorem omitting_only_incarnation_freshness_revives_stale_ptr :
    InitializeStep sites True True start location pkgA domain ⟨1⟩ ⟨1⟩ first ∧
    TakeStep True first location (root pkgA 1 1) domain taken ∧
    WellFormed taken ∧ ¬ LiveIncarnation taken oldPtr.incarnation ∧
    ¬ AcquireRef True True taken oldPtr domain ∧
    oldPtr.incarnation ∈ taken.usedIncarnations ∧
    InitializeIgnoringIncarnationFreshness True True taken ⟨1⟩ ⟨2⟩ revived ∧
    WellFormed revived ∧
    ¬ RawInitialize sites True True taken location pkgB domain ⟨1⟩ ⟨2⟩ revived ∧
    AcquireRef True True revived oldPtr domain := by
  have recorded := (take_ended_identities_remain_recorded takeFirst.1 takeFirst.2.1).1
  have wf : WellFormed revived := by
    rw [revived_eq]; exact live_wellFormed _ _ _ _ _ _ (by decide) (by simp) (by simp)
  refine ⟨initializeFirst, takeFirst, takeFirst.2.2, take_ends_incarnation takeFirst.1 takeFirst.2.1,
    stale_ptr_after_take_cannot_acquire_ref takeFirst.1 takeFirst.2.1 rfl, recorded, ?_, wf,
    initialize_rejects_reused_incarnation recorded, ?_⟩
  · refine ⟨take_restores_vacancy takeFirst.2.1, ?_, ?_, ?_, True.intro, True.intro, rfl⟩ <;>
      simp [taken_eq, fixture, FreshValueFact]
  · refine ⟨wf, ⟨⟨root pkgB 1 2, ?_, rfl, rfl⟩, True.intro, True.intro⟩⟩
    simp [revived, initializeCandidate, oldPtr, ptrFromInitialize, root]

private def AcquireIgnoringIncarnation (stable access : Prop) (s : State) (ptr : PtrToken)
    (evidenceDomain : DomainId) : Prop :=
  WellFormed s ∧ (∃ r, s.occupancy ptr.location = .live r ∧ r.governing = evidenceDomain) ∧ stable ∧ access
private def AcquireIgnoringDomain (stable access : Prop) (s : State) (ptr : PtrToken)
    (_evidenceDomain : DomainId) : Prop := WellFormed s ∧ CurrentPtr s ptr ∧ stable ∧ access

theorem omitting_incarnation_match_accepts_old_ptr_after_fresh_reinitialize :
    InitializeStep sites True True taken location pkgB domain ⟨2⟩ ⟨2⟩ (restarted taken) ∧
    AcquireIgnoringIncarnation True True (restarted taken) oldPtr domain ∧
    ¬ AcquireRef True True (restarted taken) oldPtr domain :=
  ⟨reinitializeTaken, ⟨reinitializeTaken.2.2,
    ⟨root pkgB 2 2, reinitializeTaken.2.1.target_after, rfl⟩, True.intro, True.intro⟩,
   take_then_reinitialize_does_not_revive_old_ptr takeFirst.1 takeFirst.2.1 reinitializeTaken.2.1⟩

theorem omitting_domain_match_accepts_wrong_live_domain :
    wrongDomain ∈ first.liveDomains ∧
    AcquireIgnoringDomain True True first oldPtr wrongDomain ∧
    ¬ AcquireRef True True first oldPtr wrongDomain :=
  ⟨by simp [first_eq, fixture], ⟨initializeFirst.2.2,
    (initialize_yields_current_ptr initializeFirst).2.2.2, True.intro, True.intro⟩,
   acquire_ref_rejects_wrong_domain initializeFirst.2.1.target_after (by decide)⟩

end NewLang.F0.Counterexample.Reference
