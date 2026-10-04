import NewLang.F0.Replace

/-! Concrete replace validation, separated from the production kernel namespace.
The raw relation is used as the intentionally unchecked rule; no broken production Step is added. -/
namespace NewLang.F0.Counterexample.Replace

private def location : RootLocationId := ⟨0⟩
private def oldPackage : PackageId := ⟨0⟩
private def incomingPackage : PackageId := ⟨1⟩
private def freshFact : ValueFactId := ⟨1⟩
private def retiredFact : ValueFactId := ⟨2⟩
private def initialRoot : LiveRoot := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, oldPackage, ⟨0⟩⟩
private def oldAtom : Fact := .valueFact initialRoot.place initialRoot.currentFact

private def package (dependent : Bool) : ValuePackage where
  dependencies := if dependent then {oldAtom} else ∅
  discardable := true

/-- A self-dependent old value and/or incoming value are valid while the old fact is live.
The history also retains a dead, previously allocated identity (2). -/
private def before (oldDependent incomingDependent : Bool) : State where
  occupancy := fun l => if l = location then .live initialRoot else .vacant
  packages := fun p =>
    if p = oldPackage then some (package oldDependent)
    else if p = incomingPackage then some (package incomingDependent) else none
  loosePackages := {incomingPackage}
  liveDomains := {initialRoot.governing}
  usedValueFacts := {initialRoot.currentFact, retiredFact}
  usedIncarnations := {initialRoot.incarnation}

private def after (oldDependent incomingDependent : Bool) : State :=
  replaceCandidate (before oldDependent incomingDependent) location initialRoot incomingPackage freshFact

private theorem before_live_iff {oldDependent incomingDependent : Bool}
    {l : RootLocationId} {r : LiveRoot} :
    (before oldDependent incomingDependent).occupancy l = .live r ↔
      l = location ∧ r = initialRoot := by
  by_cases same : l = location
  · simp [before, same, eq_comm]
  · simp [before, same]

private theorem before_installed_iff {oldDependent incomingDependent : Bool} {pkg : PackageId} :
    IsInstalled (before oldDependent incomingDependent) pkg ↔ pkg = oldPackage := by
  simp only [IsInstalled, Carries, before_live_iff]
  simp [initialRoot, eq_comm]

private theorem before_survives_iff {oldDependent incomingDependent : Bool} {pkg : PackageId} :
    Survives (before oldDependent incomingDependent) pkg ↔
      pkg = oldPackage ∨ pkg = incomingPackage := by
  simp only [Survives, before_installed_iff]
  simp [before]

private theorem oldAtom_live (oldDependent incomingDependent : Bool) :
    oldAtom ∈ LiveFacts (before oldDependent incomingDependent) :=
  ⟨location, initialRoot, by simp [before], rfl, rfl⟩

/-- Both dependent and independent fixture inputs start well formed. -/
theorem before_wellFormed (oldDependent incomingDependent : Bool) :
    WellFormed (before oldDependent incomingDependent) := by
  constructor
  · intro pkg c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;>
      simp only [Carries, before_live_iff] at h₁ h₂ <;>
      simp_all [before, initialRoot, oldPackage, incomingPackage]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [before_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [before_live_iff]
  · intro pkg survivor
    rcases before_survives_iff.mp survivor with old | incoming
    · subst pkg
      exact ⟨package oldDependent, by simp [before]⟩
    · subst pkg
      exact ⟨package incomingDependent, by simp [before, oldPackage, incomingPackage]⟩
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before]
  · intro pkg value survivor present fact dependency
    rcases before_survives_iff.mp survivor with old | incoming
    · subst pkg
      have value_eq : package oldDependent = value := by
        simpa [before] using present
      subst value
      by_cases dep : oldDependent = true
      · have atom : fact = oldAtom := by simpa [package, dep] using dependency
        subst fact
        exact oldAtom_live _ _
      · simp [package, dep] at dependency
    · subst pkg
      have value_eq : package incomingDependent = value := by
        simpa [before, oldPackage, incomingPackage] using present
      subst value
      by_cases dep : incomingDependent = true
      · have atom : fact = oldAtom := by simpa [package, dep] using dependency
        subst fact
        exact oldAtom_live _ _
      · simp [package, dep] at dependency
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before]

  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before]

private theorem raw (oldDependent incomingDependent : Bool) :
    RawReplace True True (before oldDependent incomingDependent) location initialRoot
      incomingPackage freshFact (after oldDependent incomingDependent) where
  target_live := by simp [before]
  incoming_loose := by simp [before]
  fresh := by simp [FreshValueFact, before, freshFact, initialRoot, retiredFact]
  write_allowed := True.intro
  types_agree := True.intro
  post_eq := rfl

private theorem after_live_iff {oldDependent incomingDependent : Bool}
    {l : RootLocationId} {r : LiveRoot} :
    (after oldDependent incomingDependent).occupancy l = .live r ↔
      l = location ∧ r = {initialRoot with currentFact := freshFact, package := incomingPackage} := by
  by_cases same : l = location
  · simp [after, replaceCandidate, same, eq_comm]
  · simp [after, replaceCandidate, before, same]

private theorem after_survives_iff {oldDependent incomingDependent : Bool} {pkg : PackageId} :
    Survives (after oldDependent incomingDependent) pkg ↔
      pkg = incomingPackage ∨ pkg = oldPackage := by
  simp only [Survives, IsInstalled, Carries, after_live_iff]
  simp [after, replaceCandidate, before, initialRoot, eq_comm]

/-- All non-dependency invariants hold even in the deliberately malformed candidate. -/
private theorem after_structure (oldDependent incomingDependent : Bool) :
    CarrierUnique (after oldDependent incomingDependent) ∧
    PlacesUnique (after oldDependent incomingDependent) ∧
    IncarnationsUnique (after oldDependent incomingDependent) ∧
    PackagesPresent (after oldDependent incomingDependent) ∧
    DomainsValid (after oldDependent incomingDependent) ∧
    ValueFactsRecorded (after oldDependent incomingDependent) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pkg c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;>
      simp only [Carries, after_live_iff] at h₁ h₂ <;>
      simp_all [after, replaceCandidate, before, initialRoot, oldPackage, incomingPackage]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [after_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [after_live_iff]
  · intro pkg survivor
    have pre_survives : Survives (before oldDependent incomingDependent) pkg := by
      rw [before_survives_iff]
      rcases after_survives_iff.mp survivor with incoming | old
      · exact Or.inr incoming
      · exact Or.inl old
    have defined := (before_wellFormed oldDependent incomingDependent).packagesPresent pkg pre_survives
    simpa [after, replaceCandidate] using defined
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩
    simp [after, replaceCandidate, before]
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩
    simp [after, replaceCandidate]

/-- Dependency-free replacement has a legal Step: the relation is not vacuous. -/
theorem independent_replace_is_legal :
    ReplaceStep True True (before false false) location initialRoot
      incomingPackage freshFact (after false false) := by
  refine ⟨before_wellFormed _ _, raw _ _, ?_⟩
  rcases after_structure false false with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, ?_, history, ?_⟩
  · intro pkg value survivor defined fact dependency
    rcases after_survives_iff.mp survivor with incoming | old
    · subst pkg
      have value_eq : package false = value := by
        simpa [after, replaceCandidate, before, oldPackage, incomingPackage] using defined
      subst value
      simp [package] at dependency
    · subst pkg
      have value_eq : package false = value := by
        simpa [after, replaceCandidate, before] using defined
      subst value
      simp [package] at dependency
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩
    simp [after, replaceCandidate, before]

/-- Dropping the candidate dependency check admits an actual malformed raw post-state.
Every other WellFormed field holds, so the failure is specifically dependency validity. -/
theorem unchecked_replace_launders_old_dependency :
    WellFormed (before true false) ∧
    RawReplace True True (before true false) location initialRoot
      incomingPackage freshFact (after true false) ∧
    CarrierUnique (after true false) ∧ PlacesUnique (after true false) ∧
    IncarnationsUnique (after true false) ∧ PackagesPresent (after true false) ∧
    DomainsValid (after true false) ∧ ValueFactsRecorded (after true false) ∧
    ¬ DependenciesValid (after true false) := by
  refine ⟨before_wellFormed _ _, raw _ _, ?_⟩
  rcases after_structure true false with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, history, ?_⟩
  intro valid
  have survivor := (replace_old_package_survives_as_loose (raw true false)).2
  have defined : (after true false).packages oldPackage = some (package true) := by
    simp [after, replaceCandidate, before]
  have live := valid oldPackage (package true) survivor defined oldAtom (by simp [package])
  exact rawReplace_old_current_fact_not_live (before_wellFormed _ _) (raw true false) live

theorem old_dependency_is_rejected :
    ¬ ReplaceStep True True (before true false) location initialRoot
      incomingPackage freshFact (after true false) :=
  replace_rejects_surviving_old_current_dependency (value := package true) (before_wellFormed _ _)
    (by simp [before, initialRoot]) (by simp [package, oldAtom])

theorem incoming_dependency_is_rejected :
    ¬ ReplaceStep True True (before false true) location initialRoot
      incomingPackage freshFact (after false true) :=
  replace_rejects_incoming_old_current_dependency (value := package true) (before_wellFormed _ _)
    (by simp [before, oldPackage, incomingPackage]) (by simp [package, oldAtom])

/-- Identity 2 is not currently live but cannot be reused as a fresh value fact. -/
theorem currently_dead_is_not_historically_fresh :
    (∀ place, Fact.valueFact place retiredFact ∉ LiveFacts (before false false)) ∧
    ¬ FreshValueFact (before false false) retiredFact ∧
    ∀ candidate, ¬ RawReplace True True (before false false) location initialRoot
      incomingPackage retiredFact candidate := by
  refine ⟨?_, ?_, ?_⟩
  · intro place
    rintro ⟨l, r, live, _, fact⟩
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [initialRoot, retiredFact] at fact
  · simp [FreshValueFact, before]
  · intro candidate
    exact replace_rejects_previously_used_fact (by simp [before])

end NewLang.F0.Counterexample.Replace
