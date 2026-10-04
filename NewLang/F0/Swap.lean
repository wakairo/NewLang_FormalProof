import NewLang.F0.WellFormed

namespace NewLang.F0

/-- Two allocations in one transition: neither was used, and they cannot collide. -/
def FreshValueFactPair (s : State) (a b : ValueFactId) : Prop :=
  FreshValueFact s a ∧ FreshValueFact s b ∧ a ≠ b

/-- Atomic exchange of carriers. Dependencies and governing relations never retarget. -/
def swapCandidate (s : State) (left right : RootLocationId) (a b : LiveRoot)
    (freshA freshB : ValueFactId) : State where
  occupancy := fun l =>
    if l = left then .live { a with currentFact := freshA, package := b.package }
    else if l = right then .live { b with currentFact := freshB, package := a.package }
    else s.occupancy l
  packages := s.packages
  loosePackages := s.loosePackages
  liveDomains := s.liveDomains
  usedValueFacts := insert freshA (insert freshB s.usedValueFacts)

structure RawSwapSame (canWriteLeft canWriteRight typeCompatible : Prop)
    (s : State) (location : RootLocationId) (root : LiveRoot) (s' : State) : Prop where
  target_live : s.occupancy location = .live root
  write_left : canWriteLeft
  write_right : canWriteRight
  types_agree : typeCompatible
  post_eq : s' = s

structure RawSwapDistinct (canWriteLeft canWriteRight typeCompatible : Prop)
    (s : State) (left right : RootLocationId) (a b : LiveRoot)
    (freshA freshB : ValueFactId) (s' : State) : Prop where
  left_live : s.occupancy left = .live a
  right_live : s.occupancy right = .live b
  locations_distinct : left ≠ right
  fresh : FreshValueFactPair s freshA freshB
  write_left : canWriteLeft
  write_right : canWriteRight
  types_agree : typeCompatible
  post_eq : s' = swapCandidate s left right a b freshA freshB

/-- Same-place requests have no allocation arguments. This is a swap-specific sum. -/
inductive SwapCase where
  | same (location : RootLocationId) (root : LiveRoot)
  | distinct (left right : RootLocationId) (a b : LiveRoot) (freshA freshB : ValueFactId)

def RawSwap (wl wr tc : Prop) (s : State) : SwapCase → State → Prop
  | .same l r, s' => RawSwapSame wl wr tc s l r s'
  | .distinct l r a b fa fb, s' => RawSwapDistinct wl wr tc s l r a b fa fb s'

def SwapStep (wl wr tc : Prop) (s : State) (op : SwapCase) (s' : State) : Prop :=
  WellFormed s ∧ RawSwap wl wr tc s op s' ∧ WellFormed s'

abbrev SwapSameStep (wl wr tc : Prop) (s : State) (l : RootLocationId) (r : LiveRoot)
    (s' : State) := SwapStep wl wr tc s (.same l r) s'
abbrev SwapDistinctStep (wl wr tc : Prop) (s : State) (l r : RootLocationId) (a b : LiveRoot)
    (fa fb : ValueFactId) (s' : State) := SwapStep wl wr tc s (.distinct l r a b fa fb) s'

section
variable {wl wr tc : Prop} {s s' : State} {left right : RootLocationId}
  {a b : LiveRoot} {fa fb : ValueFactId}

theorem swap_same_is_identity (h : SwapSameStep wl wr tc s left a s') : s' = s := h.2.1.post_eq

theorem swap_same_preserves_history (h : SwapSameStep wl wr tc s left a s') :
    s'.usedValueFacts = s.usedValueFacts := by rw [swap_same_is_identity h]

theorem swap_same_preserves_current_fact (h : SwapSameStep wl wr tc s left a s') :
    ∃ root, s'.occupancy left = .live root ∧ root.currentFact = a.currentFact := by
  rw [swap_same_is_identity h]
  exact ⟨a, h.2.1.target_live, rfl⟩

theorem swap_same_preserves_package (h : SwapSameStep wl wr tc s left a s') :
    ∃ root, s'.occupancy left = .live root ∧ root.package = a.package := by
  rw [swap_same_is_identity h]
  exact ⟨a, h.2.1.target_live, rfl⟩

theorem same_swap_is_legal (wf : WellFormed s) (live : s.occupancy left = .live a)
    (writeLeft : wl) (writeRight : wr) (types : tc) : SwapSameStep wl wr tc s left a s :=
  ⟨wf, ⟨live, writeLeft, writeRight, types, rfl⟩, wf⟩

theorem RawSwapDistinct.targets_after
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    s'.occupancy left = .live {a with currentFact := fa, package := b.package} ∧
    s'.occupancy right = .live {b with currentFact := fb, package := a.package} := by
  rw [h.post_eq]
  simp [swapCandidate, Ne.symm h.locations_distinct]

theorem RawSwapDistinct.packages_distinct (wf : WellFormed s)
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') : a.package ≠ b.package := by
  intro same
  have carriers := wf.carrierUnique a.package (.installed left) (.installed right)
    ⟨a, h.left_live, rfl⟩ ⟨b, h.right_live, same.symm⟩
  exact h.locations_distinct (Carrier.installed.inj carriers)

theorem RawSwapDistinct.places_distinct (wf : WellFormed s)
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') : a.place ≠ b.place := by
  intro same
  exact h.locations_distinct (wf.placesUnique left right a b h.left_live h.right_live same)

theorem swap_distinct_preserves_wellFormed
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') : WellFormed s' := h.2.2

theorem swap_distinct_preserves_incarnations
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') :
    (∃ root, s'.occupancy left = .live root ∧ root.incarnation = a.incarnation) ∧
    (∃ root, s'.occupancy right = .live root ∧ root.incarnation = b.incarnation) :=
  ⟨⟨_, h.2.1.targets_after.1, rfl⟩, ⟨_, h.2.1.targets_after.2, rfl⟩⟩

theorem swap_distinct_preserves_governingDomains
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') :
    (∃ root, s'.occupancy left = .live root ∧ root.governing = a.governing) ∧
    (∃ root, s'.occupancy right = .live root ∧ root.governing = b.governing) :=
  ⟨⟨_, h.2.1.targets_after.1, rfl⟩, ⟨_, h.2.1.targets_after.2, rfl⟩⟩

theorem swap_distinct_preserves_places_and_locations
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') :
    (∃ root, s'.occupancy left = .live root ∧ root.place = a.place) ∧
    (∃ root, s'.occupancy right = .live root ∧ root.place = b.place) :=
  ⟨⟨_, h.2.1.targets_after.1, rfl⟩, ⟨_, h.2.1.targets_after.2, rfl⟩⟩

theorem swap_distinct_exchanges_packages
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    Carries s' b.package (.installed left) ∧ Carries s' a.package (.installed right) :=
  ⟨⟨_, h.targets_after.1, rfl⟩, ⟨_, h.targets_after.2, rfl⟩⟩

theorem swap_distinct_both_packages_survive
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    Survives s' a.package ∧ Survives s' b.package :=
  ⟨Or.inl ⟨right, (swap_distinct_exchanges_packages h).2⟩,
   Or.inl ⟨left, (swap_distinct_exchanges_packages h).1⟩⟩

theorem swap_distinct_preserves_loose_packages
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    s'.loosePackages = s.loosePackages := by rw [h.post_eq]; rfl

theorem swap_distinct_preserves_package_data_and_domains
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    s'.packages = s.packages ∧ s'.liveDomains = s.liveDomains := by
  rw [h.post_eq]; exact ⟨rfl, rfl⟩

theorem swap_distinct_preserves_other_locations
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') {other : RootLocationId}
    (notLeft : other ≠ left) (notRight : other ≠ right) :
    s'.occupancy other = s.occupancy other := by
  rw [h.post_eq]; simp [swapCandidate, notLeft, notRight]

theorem swap_distinct_history_monotone
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    s.usedValueFacts ⊆ s'.usedValueFacts := by
  rw [h.post_eq]
  exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

theorem swap_distinct_creates_two_fresh_current_facts
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') :
    FreshValueFactPair s fa fb ∧ fa ∈ s'.usedValueFacts ∧ fb ∈ s'.usedValueFacts ∧
    (∃ root, s'.occupancy left = .live root ∧ root.currentFact = fa) ∧
    (∃ root, s'.occupancy right = .live root ∧ root.currentFact = fb) ∧
    s.usedValueFacts ⊆ s'.usedValueFacts := by
  refine ⟨h.2.1.fresh, ?_, ?_, ⟨_, h.2.1.targets_after.1, rfl⟩,
    ⟨_, h.2.1.targets_after.2, rfl⟩, swap_distinct_history_monotone h.2.1⟩ <;>
    rw [h.2.1.post_eq] <;> simp [swapCandidate]

theorem swap_distinct_old_facts_remain_used
    (h : SwapDistinctStep wl wr tc s left right a b fa fb s') :
    a.currentFact ∈ s'.usedValueFacts ∧ b.currentFact ∈ s'.usedValueFacts :=
  ⟨swap_distinct_history_monotone h.2.1 (h.1.valueFactsRecorded left a h.2.1.left_live),
   swap_distinct_history_monotone h.2.1 (h.1.valueFactsRecorded right b h.2.1.right_live)⟩

/-- Every pre-survivor survives; package contents are never rewritten by moving carriers. -/
theorem swap_distinct_survivors_preserved
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') {pkg : PackageId}
    (survivor : Survives s pkg) : Survives s' pkg := by
  rcases survivor with ⟨other, root, live, package⟩ | loose
  · by_cases atLeft : other = left
    · subst other
      have same := Occupancy.live.inj (h.left_live.symm.trans live)
      subst root
      rw [← package]
      exact (swap_distinct_both_packages_survive h).1
    · by_cases atRight : other = right
      · subst other
        have same := Occupancy.live.inj (h.right_live.symm.trans live)
        subst root
        rw [← package]
        exact (swap_distinct_both_packages_survive h).2
      · exact Or.inl ⟨other, root,
          (swap_distinct_preserves_other_locations h atLeft atRight).trans live, package⟩
  · exact Or.inr (by rw [swap_distinct_preserves_loose_packages h]; exact loose)

theorem rawSwapDistinct_old_left_fact_not_live (wf : WellFormed s)
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    Fact.valueFact a.place a.currentFact ∉ LiveFacts s' := by
  rintro ⟨location, root, live, place, fact⟩
  by_cases same : location = left
  · subst location
    have roots := Occupancy.live.inj (h.targets_after.1.symm.trans live)
    have fresh_eq : fa = a.currentFact := by simpa [← roots] using fact
    have used := wf.valueFactsRecorded left a h.left_live
    exact h.fresh.1 (fresh_eq ▸ used)
  · by_cases opposite : location = right
    · subst location
      have roots := Occupancy.live.inj (h.targets_after.2.symm.trans live)
      have places : b.place = a.place := by simpa [← roots] using place
      exact h.places_distinct wf places.symm
    · have pre_live := (swap_distinct_preserves_other_locations h
        same opposite).symm.trans live
      exact same (wf.placesUnique location left root a pre_live h.left_live place)

theorem rawSwapDistinct_old_right_fact_not_live (wf : WellFormed s)
    (h : RawSwapDistinct wl wr tc s left right a b fa fb s') :
    Fact.valueFact b.place b.currentFact ∉ LiveFacts s' := by
  rintro ⟨location, root, live, place, fact⟩
  by_cases same : location = right
  · subst location
    have roots := Occupancy.live.inj (h.targets_after.2.symm.trans live)
    have fresh_eq : fb = b.currentFact := by simpa [← roots] using fact
    have used := wf.valueFactsRecorded right b h.right_live
    exact h.fresh.2.1 (fresh_eq ▸ used)
  · by_cases opposite : location = left
    · subst location
      have roots := Occupancy.live.inj (h.targets_after.1.symm.trans live)
      have places : a.place = b.place := by simpa [← roots] using place
      exact h.places_distinct wf places
    · have pre_live := (swap_distinct_preserves_other_locations h
        opposite same).symm.trans live
      exact same (wf.placesUnique location right root b pre_live h.right_live place)

/-- All rejection cases use the ordinary post-state dependency invariant. -/
theorem swap_rejects_surviving_old_current_dependency (wf : WellFormed s)
    {pkg : PackageId} {value : ValuePackage} (survivor : Survives s pkg)
    (present : s.packages pkg = some value) {fact : Fact} (dependency : fact ∈ value.dependencies)
    (old : fact = .valueFact a.place a.currentFact ∨ fact = .valueFact b.place b.currentFact) :
    ¬ SwapDistinctStep wl wr tc s left right a b fa fb s' := by
  intro step
  have post_present : s'.packages pkg = some value := by
    rw [(swap_distinct_preserves_package_data_and_domains step.2.1).1]; exact present
  have live := step.2.2.dependenciesValid pkg value
    (swap_distinct_survivors_preserved step.2.1 survivor) post_present fact dependency
  rcases old with rfl | rfl
  · exact rawSwapDistinct_old_left_fact_not_live wf step.2.1 live
  · exact rawSwapDistinct_old_right_fact_not_live wf step.2.1 live

theorem swap_rejects_left_self_current_dependency (wf : WellFormed s)
    (live : s.occupancy left = .live a) {value : ValuePackage}
    (present : s.packages a.package = some value)
    (dependency : Fact.valueFact a.place a.currentFact ∈ value.dependencies) :
    ¬ SwapDistinctStep wl wr tc s left right a b fa fb s' :=
  swap_rejects_surviving_old_current_dependency wf
    (Or.inl ⟨left, a, live, rfl⟩) present dependency (Or.inl rfl)

theorem swap_rejects_left_package_cross_dependency (wf : WellFormed s)
    (live : s.occupancy left = .live a) {value : ValuePackage}
    (present : s.packages a.package = some value)
    (dependency : Fact.valueFact b.place b.currentFact ∈ value.dependencies) :
    ¬ SwapDistinctStep wl wr tc s left right a b fa fb s' :=
  swap_rejects_surviving_old_current_dependency wf
    (Or.inl ⟨left, a, live, rfl⟩) present dependency (Or.inr rfl)

theorem swap_rejects_right_self_current_dependency (wf : WellFormed s)
    (live : s.occupancy right = .live b) {value : ValuePackage}
    (present : s.packages b.package = some value)
    (dependency : Fact.valueFact b.place b.currentFact ∈ value.dependencies) :
    ¬ SwapDistinctStep wl wr tc s left right a b fa fb s' :=
  swap_rejects_surviving_old_current_dependency wf
    (Or.inl ⟨right, b, live, rfl⟩) present dependency (Or.inr rfl)

theorem swap_rejects_right_package_cross_dependency (wf : WellFormed s)
    (live : s.occupancy right = .live b) {value : ValuePackage}
    (present : s.packages b.package = some value)
    (dependency : Fact.valueFact a.place a.currentFact ∈ value.dependencies) :
    ¬ SwapDistinctStep wl wr tc s left right a b fa fb s' :=
  swap_rejects_surviving_old_current_dependency wf
    (Or.inl ⟨right, b, live, rfl⟩) present dependency (Or.inl rfl)

theorem swap_rejects_reused_left_fact (used : fa ∈ s.usedValueFacts) :
    ¬ RawSwapDistinct wl wr tc s left right a b fa fb s' := by
  intro h; exact h.fresh.1 used

theorem swap_rejects_reused_right_fact (used : fb ∈ s.usedValueFacts) :
    ¬ RawSwapDistinct wl wr tc s left right a b fa fb s' := by
  intro h; exact h.fresh.2.1 used

theorem swap_rejects_colliding_new_facts (same : fa = fb) :
    ¬ RawSwapDistinct wl wr tc s left right a b fa fb s' := by
  intro h; exact h.fresh.2.2 same

end
end NewLang.F0
