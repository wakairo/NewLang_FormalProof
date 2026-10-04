import NewLang.F0.Swap

/-! Concrete swap witnesses and broken dependency validation, isolated from the kernel. -/
namespace NewLang.F0.Counterexample.Swap

private def left : RootLocationId := ⟨0⟩
private def right : RootLocationId := ⟨1⟩
private def pkgA : PackageId := ⟨0⟩
private def pkgB : PackageId := ⟨1⟩
private def pkgQ : PackageId := ⟨2⟩
private def rootA : LiveRoot := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, pkgA, ⟨0⟩⟩
private def rootB : LiveRoot := ⟨⟨1⟩, ⟨1⟩, ⟨1⟩, pkgB, ⟨1⟩⟩
private def atomA : Fact := .valueFact rootA.place rootA.currentFact
private def atomB : Fact := .valueFact rootB.place rootB.currentFact
private def freshA : ValueFactId := ⟨2⟩
private def freshB : ValueFactId := ⟨3⟩
private def retired : ValueFactId := ⟨4⟩

private def package (deps : Finset Fact) : ValuePackage := ⟨deps, false⟩

private def before (da db dq : Finset Fact) : State where
  occupancy := fun l => if l = left then .live rootA else if l = right then .live rootB else .vacant
  packages := fun p => if p = pkgA then some (package da)
    else if p = pkgB then some (package db) else if p = pkgQ then some (package dq) else none
  loosePackages := {pkgQ}
  liveDomains := {rootA.governing, rootB.governing}
  usedValueFacts := {rootA.currentFact, rootB.currentFact, retired}
  usedIncarnations := {rootA.incarnation, rootB.incarnation}

private def after (da db dq : Finset Fact) : State :=
  swapCandidate (before da db dq) left right rootA rootB freshA freshB

private theorem before_live_iff {da db dq : Finset Fact} {l : RootLocationId} {r : LiveRoot} :
    (before da db dq).occupancy l = .live r ↔
      (l = left ∧ r = rootA) ∨ (l = right ∧ r = rootB) := by
  by_cases hl : l = left
  · subst l; simp [before, left, right, eq_comm]
  · by_cases hr : l = right
    · subst l; simp [before, left, right, eq_comm]
    · simp [before, hl, hr]

private theorem before_carries_iff {da db dq : Finset Fact} {p : PackageId} {c : Carrier} :
    Carries (before da db dq) p c ↔
      (p = pkgA ∧ c = .installed left) ∨
      (p = pkgB ∧ c = .installed right) ∨ (p = pkgQ ∧ c = .loose) := by
  cases c <;> simp only [Carries, before_live_iff, or_and_right, exists_or]
  · simp [rootA, rootB, eq_comm, and_comm]
  · simp [before]

private theorem before_survives_iff {da db dq : Finset Fact} {p : PackageId} :
    Survives (before da db dq) p ↔ p = pkgA ∨ p = pkgB ∨ p = pkgQ := by
  simp only [Survives, IsInstalled, before_carries_iff, exists_or]
  simp [before, or_assoc]

private theorem dependency_live {da db dq deps : Finset Fact} {fact : Fact}
    (allowed : deps ⊆ {atomA, atomB}) (dep : fact ∈ deps) :
    fact ∈ LiveFacts (before da db dq) := by
  have atoms : fact = atomA ∨ fact = atomB := by simpa using allowed dep
  rcases atoms with rfl | rfl
  · exact ⟨left, rootA, by simp [before], rfl, rfl⟩
  · exact ⟨right, rootB, by simp [before, left, right], rfl, rfl⟩

/-- All self/cross/cyclic/third fixtures start valid while both old facts are live. -/
theorem before_wellFormed (da db dq : Finset Fact)
    (ha : da ⊆ {atomA, atomB}) (hb : db ⊆ {atomA, atomB}) (hq : dq ⊆ {atomA, atomB}) :
    WellFormed (before da db dq) := by
  constructor
  · intro p c₁ c₂ h₁ h₂
    rw [before_carries_iff] at h₁ h₂
    rcases h₁ with ⟨hp₁, hc₁⟩ | ⟨hp₁, hc₁⟩ | ⟨hp₁, hc₁⟩ <;>
      rcases h₂ with ⟨hp₂, hc₂⟩ | ⟨hp₂, hc₂⟩ | ⟨hp₂, hc₂⟩ <;>
      simp_all [pkgA, pkgB, pkgQ]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ places
    rcases before_live_iff.mp h₁ with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;>
      rcases before_live_iff.mp h₂ with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩ <;>
      simp_all [rootA, rootB]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ incarnations
    rcases before_live_iff.mp h₁ with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;>
      rcases before_live_iff.mp h₂ with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩ <;>
      simp_all [rootA, rootB]
  · intro p survivor
    rcases before_survives_iff.mp survivor with rfl | rfl | rfl
    · exact ⟨package da, by simp [before]⟩
    · exact ⟨package db, by simp [before, pkgA, pkgB]⟩
    · exact ⟨package dq, by simp [before, pkgA, pkgB, pkgQ]⟩
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [before]
  · intro p value survivor present fact dep
    rcases before_survives_iff.mp survivor with rfl | rfl | rfl
    · have same : package da = value := by simpa [before] using present
      subst value; exact dependency_live ha dep
    · have same : package db = value := by simpa [before, pkgA, pkgB] using present
      subst value; exact dependency_live hb dep
    · have same : package dq = value := by simpa [before, pkgA, pkgB, pkgQ] using present
      subst value; exact dependency_live hq dep
  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [before]

  · intro l r live
    rcases before_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [before]

private theorem raw (da db dq : Finset Fact) :
    RawSwapDistinct True True True (before da db dq) left right rootA rootB
      freshA freshB (after da db dq) where
  left_live := by simp [before]
  right_live := by simp [before, left, right]
  locations_distinct := by decide
  fresh := by simp [FreshValueFactPair, FreshValueFact, before, freshA, freshB, rootA, rootB, retired]
  write_left := True.intro
  write_right := True.intro
  types_agree := True.intro
  post_eq := rfl

private theorem after_live_iff {da db dq : Finset Fact} {l : RootLocationId} {r : LiveRoot} :
    (after da db dq).occupancy l = .live r ↔
      (l = left ∧ r = {rootA with currentFact := freshA, package := pkgB}) ∨
      (l = right ∧ r = {rootB with currentFact := freshB, package := pkgA}) := by
  by_cases hl : l = left
  · subst l; simp [after, swapCandidate, rootA, rootB, left, right, eq_comm]
  · by_cases hr : l = right
    · subst l; simp [after, swapCandidate, rootA, rootB, left, right, eq_comm]
    · simp [after, swapCandidate, before, hl, hr]

private theorem after_carries_iff {da db dq : Finset Fact} {p : PackageId} {c : Carrier} :
    Carries (after da db dq) p c ↔
      (p = pkgB ∧ c = .installed left) ∨
      (p = pkgA ∧ c = .installed right) ∨ (p = pkgQ ∧ c = .loose) := by
  cases c <;> simp only [Carries, after_live_iff, or_and_right, exists_or]
  · simp [eq_comm, and_comm]
  · simp [after, swapCandidate, before]

private theorem after_survives_iff {da db dq : Finset Fact} {p : PackageId} :
    Survives (after da db dq) p ↔ p = pkgB ∨ p = pkgA ∨ p = pkgQ := by
  simp only [Survives, IsInstalled, after_carries_iff, exists_or]
  simp [after, swapCandidate, before, or_assoc]

private theorem after_structure (da db dq : Finset Fact) :
    CarrierUnique (after da db dq) ∧ PlacesUnique (after da db dq) ∧
    IncarnationsUnique (after da db dq) ∧ PackagesPresent (after da db dq) ∧
    DomainsValid (after da db dq) ∧ ValueFactsRecorded (after da db dq) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p c₁ c₂ h₁ h₂
    rw [after_carries_iff] at h₁ h₂
    rcases h₁ with ⟨hp₁, hc₁⟩ | ⟨hp₁, hc₁⟩ | ⟨hp₁, hc₁⟩ <;>
      rcases h₂ with ⟨hp₂, hc₂⟩ | ⟨hp₂, hc₂⟩ | ⟨hp₂, hc₂⟩ <;>
      simp_all [pkgA, pkgB, pkgQ]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ places
    rcases after_live_iff.mp h₁ with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;>
      rcases after_live_iff.mp h₂ with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩ <;>
      simp_all [rootA, rootB]
  · intro l₁ l₂ r₁ r₂ h₁ h₂ incarnations
    rcases after_live_iff.mp h₁ with ⟨hl₁, hr₁⟩ | ⟨hl₁, hr₁⟩ <;>
      rcases after_live_iff.mp h₂ with ⟨hl₂, hr₂⟩ | ⟨hl₂, hr₂⟩ <;>
      simp_all [rootA, rootB]
  · intro p survivor
    rcases after_survives_iff.mp survivor with rfl | rfl | rfl
    · exact ⟨package db, by simp [after, swapCandidate, before, pkgA, pkgB]⟩
    · exact ⟨package da, by simp [after, swapCandidate, before]⟩
    · exact ⟨package dq, by simp [after, swapCandidate, before, pkgA, pkgB, pkgQ]⟩
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [after, swapCandidate, before]
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [after, swapCandidate]

/-- Non-vacuous legal distinct swap, with different governing domains and non-discardable values. -/
theorem independent_distinct_swap_is_legal :
    SwapDistinctStep True True True (before ∅ ∅ ∅) left right rootA rootB
      freshA freshB (after ∅ ∅ ∅) := by
  refine ⟨before_wellFormed _ _ _ (by simp) (by simp) (by simp), raw _ _ _, ?_⟩
  rcases after_structure ∅ ∅ ∅ with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, ?_, history, ?_⟩
  · intro p value survivor defined fact dep
    rcases after_survives_iff.mp survivor with rfl | rfl | rfl
    · have same : package ∅ = value := by simpa [after, swapCandidate, before, pkgA, pkgB] using defined
      subst value; simp [package] at dep
    · have same : package ∅ = value := by simpa [after, swapCandidate, before] using defined
      subst value; simp [package] at dep
    · have same : package ∅ = value := by simpa [after, swapCandidate, before, pkgA, pkgB, pkgQ] using defined
      subst value; simp [package] at dep
  · intro l r live
    rcases after_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [after, swapCandidate, before]

theorem swap_does_not_require_discardable :
    (before ∅ ∅ ∅).packages pkgA = some (package ∅) ∧
    (before ∅ ∅ ∅).packages pkgB = some (package ∅) ∧
    (package ∅).discardable = false ∧
    SwapDistinctStep True True True (before ∅ ∅ ∅) left right rootA rootB
      freshA freshB (after ∅ ∅ ∅) :=
  ⟨by simp [before], by simp [before, pkgA, pkgB], rfl, independent_distinct_swap_is_legal⟩

/-- Same-place allocates nothing and keeps the existing self-dependency live. -/
theorem same_place_swap_preserves_self_dependency :
    SwapSameStep True True True (before {atomA} ∅ ∅) left rootA (before {atomA} ∅ ∅) ∧
    atomA ∈ (package {atomA}).dependencies ∧
    atomA ∈ LiveFacts (before {atomA} ∅ ∅) := by
  refine ⟨same_swap_is_legal (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before]) True.intro True.intro True.intro, by simp [package], ?_⟩
  exact ⟨left, rootA, by simp [before], rfl, rfl⟩

theorem left_self_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before {atomA} ∅ ∅) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_left_self_current_dependency (value := package {atomA})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before])
    (by simp [before, rootA, rootB, pkgA, pkgB]) (by simp [package, atomA])

theorem right_self_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before ∅ {atomB} ∅) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_right_self_current_dependency (value := package {atomB})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before, left, right])
    (by simp [before, rootA, rootB, pkgA, pkgB]) (by simp [package, atomB])

theorem left_cross_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before {atomB} ∅ ∅) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_left_package_cross_dependency (value := package {atomB})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before])
    (by simp [before, rootA, rootB, pkgA, pkgB]) (by simp [package, atomB])

theorem right_cross_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before ∅ {atomA} ∅) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_right_package_cross_dependency (value := package {atomA})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before, left, right])
    (by simp [before, rootA, rootB, pkgA, pkgB]) (by simp [package, atomA])

theorem self_dependency_allows_same_swap_but_rejects_distinct_swap :
    SwapSameStep True True True (before {atomA} ∅ ∅) left rootA (before {atomA} ∅ ∅) ∧
    ∀ candidate, ¬ SwapDistinctStep True True True (before {atomA} ∅ ∅) left right rootA rootB
      freshA freshB candidate :=
  ⟨same_place_swap_preserves_self_dependency.1, left_self_dependency_is_rejected⟩

theorem swap_rejects_cyclic_dependency_laundering (candidate : State) :
    ¬ SwapDistinctStep True True True (before {atomB} {atomA} ∅) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_left_package_cross_dependency (value := package {atomB})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before]) (by simp [before, rootA]) (by simp [package, atomB])

theorem third_survivor_left_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before ∅ ∅ {atomA}) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_surviving_old_current_dependency (pkg := pkgQ) (value := package {atomA})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before_survives_iff]) (by simp [before, pkgA, pkgB, pkgQ])
    (by simp [package, atomA]) (Or.inl rfl)

theorem third_survivor_right_dependency_is_rejected (candidate : State) :
    ¬ SwapDistinctStep True True True (before ∅ ∅ {atomB}) left right rootA rootB
      freshA freshB candidate :=
  swap_rejects_surviving_old_current_dependency (pkg := pkgQ) (value := package {atomB})
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp))
    (by simp [before_survives_iff]) (by simp [before, pkgA, pkgB, pkgQ])
    (by simp [package, atomB]) (Or.inr rfl)

/-- Cyclic laundering satisfies every structural invariant; only dependency validity fails. -/
theorem unchecked_cyclic_swap_breaks_dependencies :
    WellFormed (before {atomB} {atomA} ∅) ∧
    RawSwapDistinct True True True (before {atomB} {atomA} ∅) left right rootA rootB
      freshA freshB (after {atomB} {atomA} ∅) ∧
    CarrierUnique (after {atomB} {atomA} ∅) ∧ PlacesUnique (after {atomB} {atomA} ∅) ∧
    IncarnationsUnique (after {atomB} {atomA} ∅) ∧ PackagesPresent (after {atomB} {atomA} ∅) ∧
    DomainsValid (after {atomB} {atomA} ∅) ∧ ValueFactsRecorded (after {atomB} {atomA} ∅) ∧
    ¬ DependenciesValid (after {atomB} {atomA} ∅) := by
  refine ⟨before_wellFormed _ _ _ (by simp) (by simp) (by simp), raw _ _ _, ?_⟩
  rcases after_structure {atomB} {atomA} ∅ with ⟨carriers, places, incarnations, present, domains, history⟩
  refine ⟨carriers, places, incarnations, present, domains, history, ?_⟩
  intro valid
  have survivor : Survives (after {atomB} {atomA} ∅) pkgA := by simp [after_survives_iff]
  have defined : (after {atomB} {atomA} ∅).packages pkgA = some (package {atomB}) := by
    simp [after, swapCandidate, before]
  have live := valid pkgA (package {atomB}) survivor defined atomB (by simp [package])
  exact rawSwapDistinct_old_right_fact_not_live
    (before_wellFormed _ _ _ (by simp) (by simp) (by simp)) (raw _ _ _) live

/-- Both positions reject retired allocations; freshness alone must also reject a pair collision. -/
theorem historical_reuse_and_pair_collision_are_rejected :
    (∀ place, Fact.valueFact place retired ∉ LiveFacts (before ∅ ∅ ∅)) ∧
    (∀ candidate, ¬ RawSwapDistinct True True True (before ∅ ∅ ∅) left right rootA rootB
      retired freshB candidate) ∧
    (∀ candidate, ¬ RawSwapDistinct True True True (before ∅ ∅ ∅) left right rootA rootB
      freshA retired candidate) ∧
    FreshValueFact (before ∅ ∅ ∅) freshA ∧
    (∀ candidate, ¬ RawSwapDistinct True True True (before ∅ ∅ ∅) left right rootA rootB
      freshA freshA candidate) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro place
    rintro ⟨l, r, live, _, fact⟩
    rcases before_live_iff.mp live with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      simp [rootA, rootB, retired] at fact
  · intro candidate; exact swap_rejects_reused_left_fact (by simp [before])
  · intro candidate; exact swap_rejects_reused_right_fact (by simp [before])
  · simp [FreshValueFact, before, freshA, rootA, rootB, retired]
  · intro candidate; exact swap_rejects_colliding_new_facts rfl

end NewLang.F0.Counterexample.Swap
