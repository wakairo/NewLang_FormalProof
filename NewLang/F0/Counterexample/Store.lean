import NewLang.F0.Store
import NewLang.F0.Replace

/-! Concrete store witnesses and isolated break-tests. No unchecked rule is exported
from the production kernel; the fixture also keeps an uncarried old table record. -/
namespace NewLang.F0.Counterexample.Store

private def location : RootLocationId := ⟨0⟩
private def oldPackage : PackageId := ⟨0⟩
private def incomingPackage : PackageId := ⟨1⟩
private def thirdPackage : PackageId := ⟨2⟩
private def freshFact : ValueFactId := ⟨1⟩
private def retiredFact : ValueFactId := ⟨2⟩
private def initialRoot : LiveRoot := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, oldPackage, ⟨0⟩⟩
private def oldAtom : Fact := .valueFact initialRoot.place initialRoot.currentFact

private def package (dependent discardable : Bool) : ValuePackage where
  dependencies := if dependent then {oldAtom} else ∅
  discardable := discardable

private def before (oldDependent incomingDependent otherDependent oldDiscardable : Bool) : State where
  occupancy := fun l => if l = location then .live initialRoot else .vacant
  packages := fun p =>
    if p = oldPackage then some (package oldDependent oldDiscardable)
    else if p = incomingPackage then some (package incomingDependent false)
    else if p = thirdPackage then some (package otherDependent true) else none
  loosePackages := {incomingPackage, thirdPackage}
  liveDomains := {initialRoot.governing}
  usedValueFacts := {initialRoot.currentFact, retiredFact}

private def after (a b c d : Bool) : State :=
  storeCandidate (before a b c d) location initialRoot incomingPackage freshFact

private theorem before_live_iff {a b c d : Bool} {l : RootLocationId} {r : LiveRoot} :
    (before a b c d).occupancy l = .live r ↔ l = location ∧ r = initialRoot := by
  by_cases same : l = location
  · simp [before, same, eq_comm]
  · simp [before, same]

private theorem before_survives_iff {a b c d : Bool} {pkg : PackageId} :
    Survives (before a b c d) pkg ↔
      pkg = oldPackage ∨ pkg = incomingPackage ∨ pkg = thirdPackage := by
  simp only [Survives, IsInstalled, Carries, before_live_iff]
  simp [before, initialRoot, eq_comm]

private theorem oldAtom_live (a b c d : Bool) : oldAtom ∈ LiveFacts (before a b c d) :=
  ⟨location, initialRoot, by simp [before], rfl, rfl⟩

private theorem package_dependency_live (dependent discardable : Bool) {a b c d : Bool}
    {fact : Fact} (h : fact ∈ (package dependent discardable).dependencies) :
    fact ∈ LiveFacts (before a b c d) := by
  by_cases dep : dependent = true
  · have atom : fact = oldAtom := by simpa [package, dep] using h
    subst fact
    exact oldAtom_live _ _ _ _
  · simp [package, dep] at h

/-- All dependency/discardability combinations are initially well formed. -/
theorem before_wellFormed (a b c d : Bool) : WellFormed (before a b c d) := by
  constructor
  · intro pkg c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;>
      simp only [Carries, before_live_iff] at h₁ h₂ <;>
      simp_all [before, initialRoot, oldPackage, incomingPackage, thirdPackage]
    all_goals
      have zero : pkg = (⟨0⟩ : PackageId) := by
        first | exact h₁.2.symm | exact h₂.2.symm
      subst pkg
      simp_all
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [before_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [before_live_iff]
  · intro pkg survivor
    rcases before_survives_iff.mp survivor with old | incoming | other
    · subst pkg
      exact ⟨package a d, by simp [before]⟩
    · subst pkg
      exact ⟨package b false, by simp [before, oldPackage, incomingPackage]⟩
    · subst pkg
      exact ⟨package c true, by simp [before, oldPackage, incomingPackage, thirdPackage]⟩
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before]
  · intro pkg value survivor present fact dependency
    rcases before_survives_iff.mp survivor with old | incoming | other
    · subst pkg
      have value_eq : package a d = value := by simpa [before] using present
      subst value
      exact package_dependency_live _ _ dependency
    · subst pkg
      have value_eq : package b false = value := by
        simpa [before, oldPackage, incomingPackage] using present
      subst value
      exact package_dependency_live _ _ dependency
    · subst pkg
      have value_eq : package c true = value := by
        simpa [before, oldPackage, incomingPackage, thirdPackage] using present
      subst value
      exact package_dependency_live _ _ dependency
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [before]

private theorem raw (a b c : Bool) :
    RawStore True True (before a b c true) location initialRoot
      incomingPackage freshFact (after a b c true) where
  target_live := by simp [before]
  incoming_loose := by simp [before]
  fresh := by simp [FreshValueFact, before, freshFact, initialRoot, retiredFact]
  write_allowed := True.intro
  types_agree := True.intro
  old_discardable := ⟨package a true, by simp [before, initialRoot], rfl⟩
  post_eq := rfl

private theorem after_live_iff {a b c d : Bool} {l : RootLocationId} {r : LiveRoot} :
    (after a b c d).occupancy l = .live r ↔
      l = location ∧ r = {initialRoot with currentFact := freshFact, package := incomingPackage} := by
  by_cases same : l = location
  · simp [after, storeCandidate, same, eq_comm]
  · simp [after, storeCandidate, before, same]

private theorem after_survives_iff {a b c d : Bool} {pkg : PackageId} :
    Survives (after a b c d) pkg ↔ pkg = incomingPackage ∨ pkg = thirdPackage := by
  simp only [Survives, IsInstalled, Carries, after_live_iff]
  simp [after, storeCandidate, before, initialRoot, oldPackage, incomingPackage, thirdPackage, eq_comm]

/-- Every non-dependency invariant holds, even when discarding would be unauthorized. -/
private theorem after_structure (a b c d : Bool) :
    CarrierUnique (after a b c d) ∧ PlacesUnique (after a b c d) ∧
    IncarnationsUnique (after a b c d) ∧ PackagesPresent (after a b c d) ∧
    DomainsValid (after a b c d) ∧ ValueFactsRecorded (after a b c d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pkg c₁ c₂ h₁ h₂
    cases c₁ <;> cases c₂ <;>
      simp only [Carries, after_live_iff] at h₁ h₂ <;>
      simp_all [after, storeCandidate, before, initialRoot, oldPackage, incomingPackage, thirdPackage]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [after_live_iff]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ _
    simp_all [after_live_iff]
  · intro pkg survivor
    have pre_survives : Survives (before a b c d) pkg := by
      rw [before_survives_iff]
      rcases after_survives_iff.mp survivor with incoming | other
      · exact Or.inr (Or.inl incoming)
      · exact Or.inr (Or.inr other)
    simpa [after, storeCandidate] using
      (before_wellFormed a b c d).packagesPresent pkg pre_survives
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩
    simp [after, storeCandidate, before]
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩
    simp [after, storeCandidate]

private theorem after_wellFormed (a d : Bool) : WellFormed (after a false false d) := by
  rcases after_structure a false false d with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, ?_, history⟩
  intro pkg value survivor defined fact dependency
  rcases after_survives_iff.mp survivor with incoming | other
  · subst pkg
    have value_eq : package false false = value := by
      simpa [after, storeCandidate, before, oldPackage, incomingPackage] using defined
    subst value
    simp [package] at dependency
  · subst pkg
    have value_eq : package false true = value := by
      simpa [after, storeCandidate, before, oldPackage, incomingPackage, thirdPackage] using defined
    subst value
    simp [package] at dependency

/-- A concrete legal store consumes an old self-dependency in the same atomic transition. -/
theorem store_can_eliminate_old_only_dependency :
    oldAtom ∈ (package true true).dependencies ∧
    StoreStep True True (before true false false true) location initialRoot
      incomingPackage freshFact (after true false false true) :=
  ⟨by simp [package], before_wellFormed _ _ _ _, raw _ _ _, after_wellFormed _ _⟩

/-- Same pre-state, incoming package and fresh identity: replace rejects, store accepts. -/
theorem old_self_dependency_rejects_replace_but_allows_store :
    (∀ candidate, ¬ ReplaceStep True True (before true false false true) location initialRoot
      incomingPackage freshFact candidate) ∧
    StoreStep True True (before true false false true) location initialRoot
      incomingPackage freshFact (after true false false true) := by
  refine ⟨?_, store_can_eliminate_old_only_dependency.2⟩
  intro candidate
  exact replace_rejects_surviving_old_current_dependency (value := package true true)
    (before_wellFormed _ _ _ _) (by simp [before, initialRoot]) (by simp [package, oldAtom])

/-- Only the old carrier disappears; retaining its data does not retain its dependency. -/
theorem old_only_dependency_removed_from_validation :
    (after true false false true).packages oldPackage = some (package true true) ∧
    oldAtom ∈ (package true true).dependencies ∧
    ¬ Survives (after true false false true) oldPackage ∧
    DependenciesValid (after true false false true) := by
  refine ⟨by simp [after, storeCandidate, before], by simp [package], ?_, ?_⟩
  · exact store_old_package_does_not_survive store_can_eliminate_old_only_dependency.2
  · exact (after_wellFormed _ _).dependenciesValid

theorem incoming_need_not_be_discardable :
    (before true false false true).packages incomingPackage = some (package false false) ∧
    (package false false).discardable = false ∧
    StoreStep True True (before true false false true) location initialRoot
      incomingPackage freshFact (after true false false true) :=
  ⟨by simp [before, oldPackage, incomingPackage], rfl, store_can_eliminate_old_only_dependency.2⟩

theorem other_survivor_dependency_is_rejected (candidate : State) :
    ¬ StoreStep True True (before true false true true) location initialRoot
      incomingPackage freshFact candidate :=
  store_rejects_other_surviving_old_current_dependency (pkg := thirdPackage)
    (value := package true true) (before_wellFormed _ _ _ _)
    (by simp [before_survives_iff]) (by decide)
    (by simp [before, oldPackage, incomingPackage, thirdPackage]) (by simp [package, oldAtom])

theorem incoming_dependency_is_rejected (candidate : State) :
    ¬ StoreStep True True (before true true false true) location initialRoot
      incomingPackage freshFact candidate :=
  store_rejects_incoming_old_current_dependency (value := package true false)
    (before_wellFormed _ _ _ _) (by simp [before, oldPackage, incomingPackage])
    (by simp [package, oldAtom])

theorem nondiscardable_old_package_is_rejected (candidate : State) :
    ¬ RawStore True True (before true false false false) location initialRoot
      incomingPackage freshFact candidate :=
  store_rejects_nondiscardable_old_package (value := package true false)
    (by simp [before, initialRoot]) rfl

/-- Removing candidate dependency validation loses a third survivor's safety. -/
theorem unchecked_other_dependency_breaks_candidate :
    WellFormed (before true false true true) ∧
    RawStore True True (before true false true true) location initialRoot
      incomingPackage freshFact (after true false true true) ∧
    CarrierUnique (after true false true true) ∧ PlacesUnique (after true false true true) ∧
    IncarnationsUnique (after true false true true) ∧ PackagesPresent (after true false true true) ∧
    DomainsValid (after true false true true) ∧ ValueFactsRecorded (after true false true true) ∧
    ¬ DependenciesValid (after true false true true) := by
  refine ⟨before_wellFormed _ _ _ _, raw _ _ _, ?_⟩
  rcases after_structure true false true true with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, history, ?_⟩
  intro valid
  have survivor : Survives (after true false true true) thirdPackage := by
    simp [after_survives_iff]
  have defined : (after true false true true).packages thirdPackage = some (package true true) := by
    simp [after, storeCandidate, before, oldPackage, incomingPackage, thirdPackage]
  have live := valid thirdPackage (package true true) survivor defined oldAtom (by simp [package])
  exact rawStore_old_current_fact_not_live (before_wellFormed _ _ _ _) (raw _ _ _) live

/-- Isolated broken premise list: all structural/static store premises except discardability. -/
private def StoreIgnoringDiscardability (s s' : State) : Prop :=
  s.occupancy location = .live initialRoot ∧ incomingPackage ∈ s.loosePackages ∧
  FreshValueFact s freshFact ∧ True ∧ True ∧
  s' = storeCandidate s location initialRoot incomingPackage freshFact

/-- WellFormed alone cannot authorize discarding a non-discardable value. -/
theorem unchecked_discardability_silently_loses_package :
    WellFormed (before true false false false) ∧
    StoreIgnoringDiscardability (before true false false false) (after true false false false) ∧
    WellFormed (after true false false false) ∧
    (before true false false false).packages oldPackage = some (package true false) ∧
    (package true false).discardable = false ∧
    ¬ Survives (after true false false false) oldPackage ∧
    ¬ RawStore True True (before true false false false) location initialRoot
      incomingPackage freshFact (after true false false false) := by
  refine ⟨before_wellFormed _ _ _ _, ?_, after_wellFormed _ _, ?_, rfl, ?_,
    nondiscardable_old_package_is_rejected _⟩
  · refine ⟨by simp [before], by simp [before], ?_, True.intro, True.intro, rfl⟩
    simp [FreshValueFact, before, freshFact, initialRoot, retiredFact]
  · simp [before]
  · simp [after_survives_iff, oldPackage, incomingPackage, thirdPackage]

/-- The retained dead identity cannot be used by store either. -/
theorem currently_dead_fact_cannot_be_reused :
    (∀ place, Fact.valueFact place retiredFact ∉ LiveFacts (before true false false true)) ∧
    ∀ candidate, ¬ RawStore True True (before true false false true) location initialRoot
      incomingPackage retiredFact candidate := by
  refine ⟨?_, ?_⟩
  · intro place
    rintro ⟨l, r, live, _, fact⟩
    rcases before_live_iff.mp live with ⟨_, rfl⟩
    simp [initialRoot, retiredFact] at fact
  · intro candidate
    exact store_rejects_previously_used_fact (by simp [before])

end NewLang.F0.Counterexample.Store
