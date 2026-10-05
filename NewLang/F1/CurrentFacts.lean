import NewLang.F1.StructuralValue

namespace NewLang.F1
open F0
noncomputable section

abbrev NodeKey := RootLocationId × PlaceId

def liveNodeSupport (s : State) : Finset NodeKey :=
  s.liveRoots.biUnion (fun l => (s.root l).layout.places.image (fun p => (l, p)))

def affectedBy (s : State) (t : StructuralTarget) : Finset NodeKey := by
  classical
  exact (liveNodeSupport s).filter (fun q => q.1 = t.location ∧
    StructuralOverlap (s.root t.location).layout t.place q.2)

def FreshStructuralFacts (s : State) (support : Finset NodeKey)
    (newFact : NodeKey → ValueFactId) : Prop :=
  (∀ q ∈ support, newFact q ∉ s.usedValueFacts) ∧
  (∀ q ∈ support, ∀ r ∈ support, newFact q = newFact r → q = r)

theorem mem_live_node_support (s : State) (l : RootLocationId) (p : PlaceId) :
    (l, p) ∈ liveNodeSupport s ↔ LiveNode s l p := by
  classical
  simp [liveNodeSupport, LiveNode]

theorem mem_affectedBy {s : State} {t : StructuralTarget} {l : RootLocationId} {p : PlaceId} :
    (l, p) ∈ affectedBy s t ↔ LiveNode s l p ∧ l = t.location ∧
      StructuralOverlap (s.root t.location).layout t.place p := by
  classical
  simp [affectedBy, mem_live_node_support]

theorem target_is_affected {s : State} {t : StructuralTarget}
    (live : LiveNode s t.location t.place) : (t.location, t.place) ∈ affectedBy s t :=
  mem_affectedBy.mpr ⟨live, rfl, Or.inl rfl⟩

theorem ancestor_of_target_is_affected {s : State} {t : StructuralTarget} {p : PlaceId}
    (live : LiveNode s t.location p) (ancestor : Ancestor (s.root t.location).layout p t.place) :
    (t.location, p) ∈ affectedBy s t := mem_affectedBy.mpr ⟨live, rfl, Or.inr (Or.inr ancestor)⟩

theorem descendant_of_target_is_affected {s : State} {t : StructuralTarget} {p : PlaceId}
    (live : LiveNode s t.location p) (descendant : Ancestor (s.root t.location).layout t.place p) :
    (t.location, p) ∈ affectedBy s t := mem_affectedBy.mpr ⟨live, rfl, Or.inr (Or.inl descendant)⟩

theorem known_disjoint_live_node_is_not_affected {s : State} {t : StructuralTarget} {p : PlaceId}
    (_live : LiveNode s t.location p) (disjoint : KnownDisjoint (s.root t.location).layout t.place p) :
    (t.location, p) ∉ affectedBy s t := fun h => disjoint (mem_affectedBy.mp h).2.2

/-- Only a small pure fact-refresh helper, not a generic operation/legality framework. -/
def refreshCurrentFacts (s : State) (support : Finset NodeKey) (fresh : NodeKey → ValueFactId) : State := by
  classical
  exact { s with
    root := fun l => { s.root l with node := fun p =>
      { (s.root l).node p with currentFact := if (l, p) ∈ support then fresh (l, p) else ((s.root l).node p).currentFact } }
    usedValueFacts := s.usedValueFacts ∪ support.image fresh }

theorem refresh_current_fact (s : State) (support : Finset NodeKey) (fresh : NodeKey → ValueFactId)
    (l : RootLocationId) (p : PlaceId) :
    (((refreshCurrentFacts s support fresh).root l).node p).currentFact =
      if (l, p) ∈ support then fresh (l, p) else ((s.root l).node p).currentFact := rfl

theorem refresh_history_monotone (s : State) (support : Finset NodeKey) (fresh : NodeKey → ValueFactId) :
    s.usedValueFacts ⊆ (refreshCurrentFacts s support fresh).usedValueFacts := Finset.subset_union_left

theorem refresh_records_new_facts {s : State} {support : Finset NodeKey} {fresh : NodeKey → ValueFactId}
    {q : NodeKey} (affected : q ∈ support) :
    fresh q ∈ (refreshCurrentFacts s support fresh).usedValueFacts :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, affected, rfl⟩)

theorem fresh_structural_facts_reject_reuse {s : State} {support : Finset NodeKey}
    {fresh : NodeKey → ValueFactId} (h : FreshStructuralFacts s support fresh)
    {q : NodeKey} (affected : q ∈ support) : fresh q ∉ s.usedValueFacts := h.1 q affected

theorem fresh_structural_facts_reject_aliasing {s : State} {support : Finset NodeKey}
    {fresh : NodeKey → ValueFactId} (h : FreshStructuralFacts s support fresh)
    {q r : NodeKey} (a : q ∈ support) (b : r ∈ support) (different : q ≠ r) :
    fresh q ≠ fresh r := fun same => different (h.2 q a r b same)

/-- Any changed old fact dies; place uniqueness rules out resurrecting it at another root. -/
theorem refreshed_old_fact_not_live {s : State} (wf : WellFormed s)
    {support : Finset NodeKey} {fresh : NodeKey → ValueFactId}
    (allocation : FreshStructuralFacts s support fresh) {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s l p) (affected : (l, p) ∈ support) :
    Fact.valueFact p ((s.root l).node p).currentFact ∉
      StructuralLiveFacts (refreshCurrentFacts s support fresh) := by
  classical
  rintro ⟨m, ml, pt, fact⟩
  have same := wf.placesUnique m l p ⟨ml, pt⟩ live
  subst m
  change (if (l, p) ∈ support then fresh (l, p) else _) = _ at fact
  rw [ite_eq_left affected] at fact
  exact allocation.1 (l, p) affected (fact ▸ wf.valueFactsRecorded l p live)


theorem refreshed_current_facts_unique {s : State} (wf : WellFormed s)
    {support : Finset NodeKey} {fresh : NodeKey → ValueFactId}
    (allocation : FreshStructuralFacts s support fresh)
    {l m : RootLocationId} {p q : PlaceId} (left : LiveNode s l p) (right : LiveNode s m q)
    (same : (((refreshCurrentFacts s support fresh).root l).node p).currentFact =
      (((refreshCurrentFacts s support fresh).root m).node q).currentFact) : l = m ∧ p = q := by
  classical
  change (if (l,p) ∈ support then _ else _) = (if (m,q) ∈ support then _ else _) at same
  by_cases a : (l,p) ∈ support <;> by_cases b : (m,q) ∈ support
  · simp only [ite_eq_left a, ite_eq_left b] at same
    have eq := allocation.2 (l,p) a (m,q) b same
    exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩
  · simp only [ite_eq_left a, ite_eq_right b] at same
    exact False.elim (allocation.1 (l,p) a (same ▸ wf.valueFactsRecorded m q right))
  · simp only [ite_eq_right a, ite_eq_left b] at same
    exact False.elim (allocation.1 (m,q) b (same.symm ▸ wf.valueFactsRecorded l p left))
  · simp only [ite_eq_right a, ite_eq_right b] at same
    exact wf.currentFactsUnique l p m q left right same

theorem refreshed_current_facts_recorded {s : State} (wf : WellFormed s)
    (support : Finset NodeKey) (fresh : NodeKey → ValueFactId) {l : RootLocationId} {p : PlaceId}
    (live : LiveNode s l p) :
    (((refreshCurrentFacts s support fresh).root l).node p).currentFact ∈
      (refreshCurrentFacts s support fresh).usedValueFacts := by
  classical
  by_cases affected : (l,p) ∈ support
  · rw [refresh_current_fact, ite_eq_left affected]; exact refresh_records_new_facts affected
  · rw [refresh_current_fact, ite_eq_right affected]
    exact refresh_history_monotone _ _ _ (wf.valueFactsRecorded l p live)

end
end NewLang.F1
