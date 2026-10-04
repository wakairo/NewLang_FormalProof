import NewLang.F0.Lifetime

/-! Lifetime witnesses and deliberately omitted checks are isolated from the production kernel. -/
namespace NewLang.F0.Counterexample.Lifetime

private def location : RootLocationId := ⟨0⟩
private def oldPkg : PackageId := ⟨0⟩
private def otherPkg : PackageId := ⟨1⟩
private def domain : DomainId := ⟨0⟩
private def otherDomain : DomainId := ⟨1⟩
private def sites : RootSiteLayout where
  placeAt := fun l => ⟨l.index⟩
  injective := by intro a b same; cases a; cases b; cases same; rfl
private def root (generation : Nat) : LiveRoot :=
  initializeRoot sites location oldPkg domain ⟨generation⟩ ⟨generation⟩
private def atom (generation : Nat) : Fact := .valueFact (root generation).place (root generation).currentFact
private def value (self domainDep discard : Bool) (generation : Nat) : ValuePackage where
  dependencies := (if self then {atom generation} else ∅) ∪ (if domainDep then {.domainLive domain} else ∅)
  discardable := discard

private def before (self third discard domainDep : Bool) (generation : Nat) : State where
  occupancy := fun l => if l = location then .live (root generation) else .vacant
  packages := fun p => if p = oldPkg then some (value self domainDep discard generation)
    else if p = otherPkg then some (value third false true generation) else none
  loosePackages := {otherPkg}
  liveDomains := {domain, otherDomain}
  domainValueCarrier := fun d => if d ∈ ({domain, otherDomain} : Finset DomainId) then some ⟨d.index⟩ else none
  usedValueFacts := {⟨generation⟩, ⟨9⟩}
  usedIncarnations := {⟨generation⟩, ⟨9⟩}

private def taken (a b c d : Bool) (g : Nat) : State := takeCandidate (before a b c d g) location (root g)
private def destroyed (a b c d : Bool) (g : Nat) : State := destroyCandidate (before a b c d g) location (root g)

private theorem before_live_iff {a b c d : Bool} {g : Nat} {l : RootLocationId} {r : LiveRoot} :
    (before a b c d g).occupancy l = .live r ↔ l = location ∧ r = root g := by
  by_cases same : l = location <;> simp [before, same, eq_comm]

private theorem before_survives_iff {a b c d : Bool} {g : Nat} {p : PackageId} :
    Survives (before a b c d g) p ↔ p = oldPkg ∨ p = otherPkg := by
  simp only [Survives, IsInstalled, Carries, before_live_iff]
  simp [before, root, initializeRoot, eq_comm]

private theorem dependency_live {a b c d self dep disc : Bool} {g : Nat} {fact : Fact}
    (h : fact ∈ (value self dep disc g).dependencies) : fact ∈ LiveFacts (before a b c d g) := by
  rcases Finset.mem_union.mp h with own | dom
  · by_cases yes : self = true
    · have same : fact = atom g := by simpa [value, yes] using own
      subst fact; exact ⟨location, root g, by simp [before], rfl, rfl⟩
    · simp [yes] at own
  · by_cases yes : dep = true
    · have same : fact = .domainLive domain := by simpa [value, yes] using dom
      subst fact; change domain ∈ (before a b c d g).liveDomains; simp [before]
    · simp [yes] at dom

theorem before_wellFormed (a b c d : Bool) (g : Nat) : WellFormed (before a b c d g) := by
  constructor
  · intro p c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;> simp only [Carries, before_live_iff] at h₁ h₂ <;>
      simp_all [before, root, initializeRoot, oldPkg, otherPkg]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [before_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _; simp_all [before_live_iff]
  · intro p survivor
    rcases before_survives_iff.mp survivor with rfl | rfl
    · exact ⟨value a d c g, by simp [before]⟩
    · exact ⟨value b false true g, by simp [before, oldPkg, otherPkg]⟩
  · intro l r live; rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before, root, initializeRoot]
  · intro p v survivor present fact dependency
    rcases before_survives_iff.mp survivor with rfl | rfl
    · have same : value a d c g = v := by simpa [before] using present
      subst v; exact dependency_live dependency
    · have same : value b false true g = v := by simpa [before, oldPkg, otherPkg] using present
      subst v; exact dependency_live dependency
  · intro l r live; rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before, root, initializeRoot]
  · intro l r live; rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before, root, initializeRoot]
  · intro dom
    simp only [before]
    split <;> simp_all

private theorem rawTake (a b c d : Bool) (g : Nat) :
    RawTake True (before a b c d g) location (root g) domain (taken a b c d g) :=
  ⟨by simp [before], rfl, True.intro, rfl⟩
private theorem rawDestroy (a b d : Bool) (g : Nat) :
    RawDestroy True (before a b true d g) location (root g) domain (destroyed a b true d g) :=
  ⟨by simp [before], rfl, True.intro, ⟨value a d true g, by simp [before, root, initializeRoot], rfl⟩, rfl⟩

private theorem taken_vacant (a b c d : Bool) (g : Nat) (l : RootLocationId) :
    (taken a b c d g).occupancy l = .vacant := by
  by_cases same : l = location <;> simp [taken, takeCandidate, before, same]
private theorem destroyed_vacant (a b c d : Bool) (g : Nat) (l : RootLocationId) :
    (destroyed a b c d g).occupancy l = .vacant := by
  by_cases same : l = location <;> simp [destroyed, destroyCandidate, before, same]

/-- Private fixture helper: vacancy structurally satisfies every root-only invariant. -/
private theorem vacant_structure {s : State} (vacant : ∀ l, s.occupancy l = .vacant)
    (present : ∀ p ∈ s.loosePackages, ∃ v, s.packages p = some v) :
    CarrierUnique s ∧ PlacesUnique s ∧ IncarnationsUnique s ∧ PackagesPresent s ∧
    DomainsValid s ∧ ValueFactsRecorded s ∧ IncarnationsRecorded s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;> simp_all [Carries]
  · intro l₁ l₂ r₁ r₂ live _ _; rw [vacant] at live; cases live
  · intro l₁ l₂ r₁ r₂ live _ _; rw [vacant] at live; cases live
  · intro p survivor
    rcases survivor with ⟨l, r, live, _⟩ | loose
    · rw [vacant] at live; cases live
    · exact present p loose
  · intro l r live; rw [vacant] at live; cases live
  · intro l r live; rw [vacant] at live; cases live
  · intro l r live; rw [vacant] at live; cases live

private theorem taken_survives_iff {a b c d : Bool} {g : Nat} {p : PackageId} :
    Survives (taken a b c d g) p ↔ p = oldPkg ∨ p = otherPkg := by
  simp only [Survives, IsInstalled, Carries, taken_vacant]
  simp [taken, takeCandidate, before, root, initializeRoot]
private theorem destroyed_survives_iff {a b c d : Bool} {g : Nat} {p : PackageId} :
    Survives (destroyed a b c d g) p ↔ p = otherPkg := by
  simp only [Survives, IsInstalled, Carries, destroyed_vacant]
  simp [destroyed, destroyCandidate, before, root, initializeRoot, oldPkg, otherPkg]

private theorem taken_structure (a b c d : Bool) (g : Nat) :
    CarrierUnique (taken a b c d g) ∧ PlacesUnique (taken a b c d g) ∧
    IncarnationsUnique (taken a b c d g) ∧ PackagesPresent (taken a b c d g) ∧
    DomainsValid (taken a b c d g) ∧ ValueFactsRecorded (taken a b c d g) ∧
    IncarnationsRecorded (taken a b c d g) := by
  apply vacant_structure (taken_vacant _ _ _ _ _)
  intro p loose
  have survivor : Survives (taken a b c d g) p := Or.inr loose
  rcases taken_survives_iff.mp survivor with rfl | rfl
  · exact ⟨value a d c g, by simp [taken, takeCandidate, before]⟩
  · exact ⟨value b false true g, by simp [taken, takeCandidate, before, oldPkg, otherPkg]⟩

private theorem destroyed_structure (a b c d : Bool) (g : Nat) :
    CarrierUnique (destroyed a b c d g) ∧ PlacesUnique (destroyed a b c d g) ∧
    IncarnationsUnique (destroyed a b c d g) ∧ PackagesPresent (destroyed a b c d g) ∧
    DomainsValid (destroyed a b c d g) ∧ ValueFactsRecorded (destroyed a b c d g) ∧
    IncarnationsRecorded (destroyed a b c d g) := by
  apply vacant_structure (destroyed_vacant _ _ _ _ _)
  intro p loose
  have survivor : Survives (destroyed a b c d g) p := Or.inr loose
  have same := destroyed_survives_iff.mp survivor
  subst p
  exact ⟨value b false true g, by simp [destroyed, destroyCandidate, before, oldPkg, otherPkg]⟩

private theorem domain_only_dependencies {s : State} {dep disc : Bool} {g : Nat}
    (domain_live : domain ∈ s.liveDomains) :
    ∀ fact ∈ (value false dep disc g).dependencies, fact ∈ LiveFacts s := by
  intro fact dependency
  by_cases yes : dep = true
  · have same : fact = .domainLive domain := by simpa [value, yes] using dependency
    subst fact; exact domain_live
  · simp [value, yes] at dependency

private theorem taken_wellFormed (discard domainDep : Bool) (g : Nat) :
    WellFormed (taken false false discard domainDep g) := by
  rcases taken_structure false false discard domainDep g with ⟨cu, pu, iu, pp, dv, vf, inc⟩
  refine ⟨cu, pu, iu, pp, dv, ?_, vf, inc,
    (before_wellFormed false false discard domainDep g).domainCarrierCoherent⟩
  intro p v survivor defined fact dependency
  rcases taken_survives_iff.mp survivor with rfl | rfl
  · have same : value false domainDep discard g = v := by simpa [taken, takeCandidate, before] using defined
    subst v; exact domain_only_dependencies (by simp [taken, takeCandidate, before]) fact dependency
  · have same : value false false true g = v := by
      simpa [taken, takeCandidate, before, oldPkg, otherPkg] using defined
    subst v; simp [value] at dependency

private theorem destroyed_wellFormed (self discard domainDep : Bool) (g : Nat) :
    WellFormed (destroyed self false discard domainDep g) := by
  rcases destroyed_structure self false discard domainDep g with ⟨cu, pu, iu, pp, dv, vf, inc⟩
  refine ⟨cu, pu, iu, pp, dv, ?_, vf, inc,
    (before_wellFormed self false discard domainDep g).domainCarrierCoherent⟩
  intro p v survivor defined fact dependency
  have samePkg := destroyed_survives_iff.mp survivor
  subst p
  have same : value false false true g = v := by
    simpa [destroyed, destroyCandidate, before, oldPkg, otherPkg] using defined
  subst v; simp [value] at dependency

theorem independent_take_is_legal (discard domainDep : Bool) (g : Nat) :
    TakeStep True (before false false discard domainDep g) location (root g) domain
      (taken false false discard domainDep g) :=
  ⟨before_wellFormed _ _ _ _ _, rawTake _ _ _ _ _, taken_wellFormed _ _ _⟩

theorem take_accepts_nondiscardable_value :
    (value false true false 0).discardable = false ∧
    TakeStep True (before false false false true 0) location (root 0) domain
      (taken false false false true 0) := ⟨rfl, independent_take_is_legal _ _ _⟩

theorem take_preserves_domain_live_dependency :
    Fact.domainLive domain ∈ (value false true false 0).dependencies ∧
    TakeStep True (before false false false true 0) location (root 0) domain
      (taken false false false true 0) ∧
    Fact.domainLive domain ∈ LiveFacts (taken false false false true 0) :=
  ⟨by simp [value], independent_take_is_legal _ _ _, take_does_not_finalize_domain (before_wellFormed _ _ _ _ _) (rawTake _ _ _ _ _)⟩

theorem independent_destroy_is_legal :
    DestroyStep True (before false false true false 0) location (root 0) domain
      (destroyed false false true false 0) :=
  ⟨before_wellFormed _ _ _ _ _, rawDestroy _ _ _ _, destroyed_wellFormed _ _ _ _⟩

theorem destroy_can_eliminate_old_only_dependency :
    atom 0 ∈ (value true false true 0).dependencies ∧
    DestroyStep True (before true false true false 0) location (root 0) domain
      (destroyed true false true false 0) :=
  ⟨by simp [value], before_wellFormed _ _ _ _ _, rawDestroy _ _ _ _, destroyed_wellFormed _ _ _ _⟩

theorem old_self_dependency_rejects_take_but_allows_destroy :
    (∀ candidate, ¬ TakeStep True (before true false true false 0) location (root 0) domain candidate) ∧
    DestroyStep True (before true false true false 0) location (root 0) domain
      (destroyed true false true false 0) := by
  refine ⟨?_, destroy_can_eliminate_old_only_dependency.2⟩
  intro candidate
  exact take_rejects_old_self_current_dependency (value := value true false true 0)
    (before_wellFormed _ _ _ _ _) (by simp [before])
    (by simp [before, root, initializeRoot]) (by simp [value, atom])

theorem third_survivor_rejects_take (candidate : State) :
    ¬ TakeStep True (before false true true false 0) location (root 0) domain candidate :=
  take_rejects_surviving_old_current_dependency (pkg := otherPkg) (value := value true false true 0)
    (before_wellFormed _ _ _ _ _) (by simp [before_survives_iff])
    (by simp [before, oldPkg, otherPkg]) (by simp [value, atom])

theorem third_survivor_rejects_destroy (candidate : State) :
    ¬ DestroyStep True (before false true true false 0) location (root 0) domain candidate :=
  destroy_rejects_other_surviving_old_current_dependency (pkg := otherPkg) (value := value true false true 0)
    (before_wellFormed _ _ _ _ _) (by simp [before_survives_iff]) (by decide)
    (by simp [before, oldPkg, otherPkg]) (by simp [value, atom])

theorem nondiscardable_destroy_is_rejected (candidate : State) :
    ¬ RawDestroy True (before false false false false 0) location (root 0) domain candidate :=
  destroy_rejects_nondiscardable_old_package (value := value false false false 0)
    (by simp [before, root, initializeRoot]) rfl

/-- Isolated omitted-guard rule; normal destroy never drops its applicability condition. -/
private def DestroyIgnoringDiscardability (s s' : State) : Prop :=
  s.occupancy location = .live (root 0) ∧ domain = (root 0).governing ∧ True ∧
    s' = destroyCandidate s location (root 0)

theorem unchecked_destroy_without_discardability_loses_nondiscardable_package :
    WellFormed (before false false false false 0) ∧
    DestroyIgnoringDiscardability (before false false false false 0) (destroyed false false false false 0) ∧
    WellFormed (destroyed false false false false 0) ∧
    (value false false false 0).discardable = false ∧
    ¬ Survives (destroyed false false false false 0) oldPkg ∧
    ¬ RawDestroy True (before false false false false 0) location (root 0) domain
      (destroyed false false false false 0) :=
  ⟨before_wellFormed _ _ _ _ _, ⟨by simp [before], rfl, True.intro, rfl⟩,
   destroyed_wellFormed _ _ _ _, rfl, by simp [destroyed_survives_iff, oldPkg, otherPkg],
   nondiscardable_destroy_is_rejected _⟩


/-- Take's unchecked raw self-dependent result violates only dependency validity. -/
theorem unchecked_take_breaks_dependencies :
    WellFormed (before true false true false 0) ∧
    RawTake True (before true false true false 0) location (root 0) domain (taken true false true false 0) ∧
    CarrierUnique (taken true false true false 0) ∧ PlacesUnique (taken true false true false 0) ∧
    IncarnationsUnique (taken true false true false 0) ∧ PackagesPresent (taken true false true false 0) ∧
    DomainsValid (taken true false true false 0) ∧ ValueFactsRecorded (taken true false true false 0) ∧
    IncarnationsRecorded (taken true false true false 0) ∧ ¬ DependenciesValid (taken true false true false 0) := by
  refine ⟨before_wellFormed _ _ _ _ _, rawTake _ _ _ _ _, ?_⟩
  rcases taken_structure true false true false 0 with ⟨cu, pu, iu, pp, dv, vf, inc⟩
  refine ⟨cu, pu, iu, pp, dv, vf, inc, ?_⟩
  intro valid
  have live := valid oldPkg (value true false true 0)
    (by simp [taken_survives_iff]) (by simp [taken, takeCandidate, before]) (atom 0) (by simp [value])
  exact take_old_current_fact_not_live (before_wellFormed _ _ _ _ _) (rawTake _ _ _ _ _) live

theorem unchecked_destroy_third_dependency_breaks_candidate :
    WellFormed (before false true true false 0) ∧
    RawDestroy True (before false true true false 0) location (root 0) domain (destroyed false true true false 0) ∧
    CarrierUnique (destroyed false true true false 0) ∧ PlacesUnique (destroyed false true true false 0) ∧
    IncarnationsUnique (destroyed false true true false 0) ∧ PackagesPresent (destroyed false true true false 0) ∧
    DomainsValid (destroyed false true true false 0) ∧ ValueFactsRecorded (destroyed false true true false 0) ∧
    IncarnationsRecorded (destroyed false true true false 0) ∧ ¬ DependenciesValid (destroyed false true true false 0) := by
  refine ⟨before_wellFormed _ _ _ _ _, rawDestroy _ _ _ _, ?_⟩
  rcases destroyed_structure false true true false 0 with ⟨cu, pu, iu, pp, dv, vf, inc⟩
  refine ⟨cu, pu, iu, pp, dv, vf, inc, ?_⟩
  intro valid
  have live := valid otherPkg (value true false true 0)
    (by simp [destroyed_survives_iff]) (by simp [destroyed, destroyCandidate, before, oldPkg, otherPkg])
    (atom 0) (by simp [value])
  exact destroy_old_current_fact_not_live (before_wellFormed _ _ _ _ _) (rawDestroy _ _ _ _) live

private def start : State where
  occupancy := fun _ => .vacant
  packages := (before false false false true 1).packages
  loosePackages := {oldPkg, otherPkg}
  liveDomains := {domain, otherDomain}
  domainValueCarrier := fun d => if d ∈ ({domain, otherDomain} : Finset DomainId) then some ⟨d.index⟩ else none
  usedValueFacts := {⟨9⟩}
  usedIncarnations := {⟨9⟩}
private def first : State := initializeCandidate sites start location oldPkg domain ⟨1⟩ ⟨1⟩
private def second : State := takeCandidate first location (root 1)
private def third : State := initializeCandidate sites second location oldPkg domain ⟨2⟩ ⟨2⟩

private theorem first_eq_before : first = before false false false true 1 := by
  simp [first, initializeCandidate, start, before, root, initializeRoot, oldPkg, otherPkg]
private theorem second_eq_taken : second = taken false false false true 1 := by
  rw [second, first_eq_before]; rfl

private theorem start_wellFormed : WellFormed start := by
  have struct := vacant_structure (s := start) (by intro l; rfl) (by
    intro p loose
    have cases : p = oldPkg ∨ p = otherPkg := by simpa [start] using loose
    rcases cases with rfl | rfl
    · exact ⟨value false true false 1, by simp [start, before]⟩
    · exact ⟨value false false true 1, by simp [start, before, oldPkg, otherPkg]⟩)
  rcases struct with ⟨cu, pu, iu, pp, dv, vf, inc⟩
  refine ⟨cu, pu, iu, pp, dv, ?_, vf, inc,
    by intro dom; simp only [start]; split <;> simp_all⟩
  intro p v survivor present fact dep
  have loose : p ∈ start.loosePackages := by
    rcases survivor with ⟨l, r, live, _⟩ | loose
    · simp [start] at live
    · exact loose
  have cases : p = oldPkg ∨ p = otherPkg := by simpa [start] using loose
  rcases cases with rfl | rfl
  · have same : value false true false 1 = v := by simpa [start, before] using present
    subst v; exact domain_only_dependencies (by simp [start]) fact dep
  · have same : value false false true 1 = v := by simpa [start, before, oldPkg, otherPkg] using present
    subst v; simp [value] at dep

private theorem rawFirst : RawInitialize sites True True start location oldPkg domain ⟨1⟩ ⟨1⟩ first :=
  ⟨rfl, by simp [start], by simp [start], by simp [FreshIncarnation, start],
   by simp [FreshValueFact, start], True.intro, True.intro, rfl⟩

theorem initialize_accepts_nondiscardable_value :
    start.packages oldPkg = some (value false true false 1) ∧
    (value false true false 1).discardable = false ∧
    InitializeStep sites True True start location oldPkg domain ⟨1⟩ ⟨1⟩ first := by
  refine ⟨by simp [start, before], rfl, start_wellFormed, rawFirst, ?_⟩
  rw [first_eq_before]; exact before_wellFormed _ _ _ _ _

private theorem takeFirst : TakeStep True first location (root 1) domain second := by
  rw [first_eq_before, second_eq_taken]
  exact independent_take_is_legal _ _ _

/-- One affine occupancy site and its package carrier are restored; histories need not roll back. -/
theorem initialize_then_take_conserves_occupancy_responsibility :
    InitializeStep sites True True start location oldPkg domain ⟨1⟩ ⟨1⟩ first ∧
    TakeStep True first location (root 1) domain second ∧
    start.occupancy location = .vacant ∧ Carries start oldPkg .loose ∧ second.occupancy location = .vacant ∧
    Carries first oldPkg (.installed location) ∧
    (∀ carrier, Carries first oldPkg carrier → carrier = .installed location) ∧
    Carries second oldPkg .loose ∧
    (∀ carrier, Carries second oldPkg carrier → carrier = .loose) :=
  ⟨initialize_accepts_nondiscardable_value.2.2, takeFirst, rfl, rawFirst.incoming_loose,
   take_restores_vacancy takeFirst.2.1, (initialize_installs_package rawFirst).1,
   initialize_package_unique_installed_carrier initialize_accepts_nondiscardable_value.2.2,
   (take_old_package_survives_as_loose takeFirst.2.1).1,
   take_old_package_unique_loose_carrier takeFirst⟩

private theorem rawThird : RawInitialize sites True True second location oldPkg domain ⟨2⟩ ⟨2⟩ third := by
  refine ⟨take_restores_vacancy takeFirst.2.1, ?_, ?_, ?_, ?_, True.intro, True.intro, rfl⟩
  · exact (take_old_package_survives_as_loose takeFirst.2.1).1
  · rw [second_eq_taken]; simp [taken, takeCandidate, before]
  · rw [second_eq_taken]; simp [FreshIncarnation, taken, takeCandidate, before]
  · rw [second_eq_taken]; simp [FreshValueFact, taken, takeCandidate, before]

/-- Incarnation/history extension of the one-root fixture, with retained prior allocations. -/
private theorem third_wellFormed : WellFormed third := by
  have base := before_wellFormed false false false true 2
  have equivalent : third =
      { before false false false true 2 with
        usedIncarnations := {⟨2⟩, ⟨1⟩, ⟨9⟩}
        usedValueFacts := {⟨2⟩, ⟨1⟩, ⟨9⟩} } := by
    simp [third, second, first, initializeCandidate, takeCandidate, start, before, root, initializeRoot,
      value, oldPkg, otherPkg]
    funext l
    by_cases same : l = location <;> simp [same]
  rw [equivalent]
  refine ⟨base.carrierUnique, base.placesUnique, base.incarnationsUnique, base.packagesPresent,
    base.domainsValid, base.dependenciesValid, ?_, ?_, base.domainCarrierCoherent⟩
  · intro l r live; rcases (before_live_iff (a := false) (b := false) (c := false) (d := true) (g := 2)).mp live with ⟨_, rfl⟩
    simp [root, initializeRoot]
  · intro l r live; rcases (before_live_iff (a := false) (b := false) (c := false) (d := true) (g := 2)).mp live with ⟨_, rfl⟩
    simp [root, initializeRoot]

theorem reinitialize_same_location_uses_fresh_incarnation :
    InitializeStep sites True True second location oldPkg domain ⟨2⟩ ⟨2⟩ third ∧
    (⟨2⟩ : IncarnationId) ≠ ⟨1⟩ ∧ (⟨2⟩ : ValueFactId) ≠ ⟨1⟩ ∧
    (⟨1⟩ : IncarnationId) ∈ second.usedIncarnations ∧ (⟨1⟩ : ValueFactId) ∈ second.usedValueFacts ∧
    FreshIncarnation second ⟨2⟩ ∧ FreshValueFact second ⟨2⟩ ∧
    third.occupancy location = .live (root 2) ∧ (root 2).place = (root 1).place := by
  refine ⟨⟨takeFirst.2.2, rawThird, third_wellFormed⟩, by decide, by decide, ?_, ?_,
    rawThird.fresh_incarnation, rawThird.fresh_fact, rawThird.target_after, rfl⟩
  · exact (take_ended_identities_remain_recorded takeFirst.1 takeFirst.2.1).1
  · exact (take_ended_identities_remain_recorded takeFirst.1 takeFirst.2.1).2

theorem dead_historical_incarnation_cannot_be_reused :
    ¬ LiveIncarnation second ⟨1⟩ ∧
    ∀ candidate, ¬ RawInitialize sites True True second location oldPkg domain ⟨1⟩ ⟨2⟩ candidate :=
  ⟨take_ends_incarnation takeFirst.1 takeFirst.2.1,
   fun _ => initialize_rejects_reused_incarnation (take_ended_identities_remain_recorded takeFirst.1 takeFirst.2.1).1⟩

theorem historical_value_fact_reuse_is_rejected (candidate : State) :
    ¬ RawInitialize sites True True second location oldPkg domain ⟨2⟩ ⟨1⟩ candidate :=
  initialize_rejects_reused_current_fact (take_ended_identities_remain_recorded takeFirst.1 takeFirst.2.1).2

theorem wrong_domain_and_missing_authority_are_rejected (candidate : State) :
    (¬ RawTake True (before false false true false 0) location (root 0) otherDomain candidate) ∧
    (¬ RawDestroy True (before false false true false 0) location (root 0) otherDomain candidate) ∧
    (¬ RawTake False (before false false true false 0) location (root 0) domain candidate) ∧
    (¬ RawDestroy False (before false false true false 0) location (root 0) domain candidate) :=
  ⟨take_rejects_wrong_ending_domain (by decide), destroy_rejects_wrong_ending_domain (by decide),
   take_rejects_missing_authority not_false, destroy_rejects_missing_authority not_false⟩

theorem dead_domain_and_missing_initialize_authority_are_rejected (candidate : State) :
    (¬ RawInitialize sites True True start location oldPkg ⟨2⟩ ⟨1⟩ ⟨1⟩ candidate) ∧
    (¬ RawInitialize sites False True start location oldPkg domain ⟨1⟩ ⟨1⟩ candidate) :=
  ⟨initialize_rejects_dead_domain (by simp [start, domain, otherDomain]),
   initialize_rejects_missing_authority not_false⟩

end NewLang.F0.Counterexample.Lifetime
