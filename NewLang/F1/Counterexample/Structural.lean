import NewLang.F1.Erasure

/-! Nontrivial controls and private malformed/omitted-rule witnesses. -/
namespace NewLang.F1.Counterexample.Structural
open F0
noncomputable section

private def rootPlace : PlaceId := ⟨0⟩
private def leftPlace : PlaceId := ⟨1⟩
private def rightPlace : PlaceId := ⟨2⟩
private def nestedPlace : PlaceId := ⟨3⟩
private def location : RootLocationId := ⟨0⟩
private def packageId : PackageId := ⟨0⟩
private def domain : DomainId := ⟨0⟩
private def childAtom : Fact := .valueFact leftPlace ⟨1⟩
private def rootAtom : Fact := .valueFact rootPlace ⟨0⟩

private def path (p : PlaceId) : List Nat :=
  if p = rootPlace then [] else if p = leftPlace then [0] else if p = rightPlace then [1] else [0, 0]
private def layout (nested : Bool) : StructuralLayout where
  places := if nested then {rootPlace, leftPlace, rightPlace, nestedPlace} else {rootPlace, leftPlace, rightPlace}
  root := rootPlace
  path := path

private theorem tracked_cases {n : Bool} {p : PlaceId} (h : p ∈ (layout n).places) :
    p = rootPlace ∨ p = leftPlace ∨ p = rightPlace ∨ p = nestedPlace := by
  cases n
  · simp only [layout, Bool.false_eq_true, ite_false, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · simpa [layout] using h

private theorem tree_wellFormed (n : Bool) : TreeWellFormed (layout n) := by
  constructor
  · cases n <;> simp [layout]
  · simp [layout, path]
  · intro p pt q qt same
    rcases tracked_cases pt with rfl | rfl | rfl | rfl <;>
      rcases tracked_cases qt with rfl | rfl | rfl | rfl <;>
      simp_all [layout, path, rootPlace, leftPlace, rightPlace, nestedPlace]
  · intro p pt nonroot
    rcases tracked_cases pt with rfl | rfl | rfl | rfl
    · exact False.elim (nonroot rfl)
    · exact ⟨rootPlace, (tree_wellFormed_root n), 0, by simp [layout, path, rootPlace, leftPlace]⟩
    · exact ⟨rootPlace, (tree_wellFormed_root n), 1, by simp [layout, path, rootPlace, leftPlace, rightPlace]⟩
    · refine ⟨leftPlace, ?_, 0, ?_⟩
      · cases n <;> simp [layout]
      · simp [layout, path, rootPlace, leftPlace, rightPlace, nestedPlace]
where
  tree_wellFormed_root (n : Bool) : rootPlace ∈ (layout n).places := by cases n <;> simp [layout]

private def node (dep : Bool) (p : PlaceId) : StructuralNodeState where
  incarnation := ⟨p.index⟩
  currentFact := ⟨p.index⟩
  localDeps := if dep = true ∧ p = leftPlace then {childAtom} else ∅
private def object (nested dep : Bool) : StructuredRoot :=
  ⟨layout nested, node dep, packageId, domain, false⟩
private def fixture (nested dep : Bool) : State where
  liveRoots := {location}
  root := fun _ => object nested dep
  loosePackages := ∅
  looseValues := fun _ => none
  liveDomains := {domain}
  domainValueCarrier := fun d => if d = domain then some ⟨0⟩ else none
  usedValueFacts := (layout nested).places.image (fun p => (⟨p.index⟩ : ValueFactId))
  usedIncarnations := (layout nested).places.image (fun p => (⟨p.index⟩ : IncarnationId))

private theorem fixture_wellFormed (nested dep : Bool) : WellFormed (fixture nested dep) := by
  constructor
  · intro l _; exact tree_wellFormed nested
  · intro l m p lh mh; exact (Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm
  · intro l p m q lh mh same
    have loc : l = m := (Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm
    refine ⟨loc, ?_⟩
    cases p; cases q; simpa [fixture, object, node] using same
  · intro l p m q lh mh same
    have loc : l = m := (Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm
    refine ⟨loc, ?_⟩
    cases p; cases q; simpa [fixture, object, node] using same
  · intro l lt m mt _; exact (Finset.mem_singleton.mp lt).trans (Finset.mem_singleton.mp mt).symm
  · intro l _; simp [fixture]
  · simp [fixture]
  · intro l _; simp [fixture, object]
  · intro l p _ fact owned
    by_cases yes : dep = true ∧ p = leftPlace
    · have atom : fact = childAtom := by simpa [LocalDeps, fixture, object, node, yes] using owned
      subst fact
      refine ⟨location, by simp [fixture], ?_, rfl⟩
      cases nested <;> simp [fixture, object, layout]
    · simp [LocalDeps, fixture, object, node, yes] at owned
  · simp [fixture]
  · intro l p live
    exact Finset.mem_image.mpr ⟨p, live.2, rfl⟩
  · intro l p live
    exact Finset.mem_image.mpr ⟨p, live.2, rfl⟩
  · intro d; by_cases same : d = domain <;> simp [fixture, same]

theorem simple_pair_is_wellFormed : WellFormed (fixture false true) := fixture_wellFormed _ _

theorem simple_pair_erases_to_wellFormed_f0 : F0.WellFormed (eraseToF0 (fixture false true)) :=
  f1_wellFormed_erases_to_f0_wellFormed simple_pair_is_wellFormed

theorem nested_structure_is_wellFormed : WellFormed (fixture true true) := fixture_wellFormed _ _

private theorem pair_siblings : Siblings (layout false) leftPlace rightPlace := by
  refine ⟨by decide, rootPlace, ?_, ?_⟩
  · exact ⟨by simp [layout], by simp [layout], 0, by simp [layout, path, rootPlace, leftPlace]⟩
  · exact ⟨by simp [layout], by simp [layout], 1, by simp [layout, path, rootPlace, leftPlace, rightPlace]⟩

theorem pair_overlap_and_disjointness :
    StructuralOverlap (layout false) rootPlace rootPlace ∧
    StructuralOverlap (layout false) rootPlace leftPlace ∧
    StructuralOverlap (layout false) leftPlace rootPlace ∧
    KnownDisjoint (layout false) leftPlace rightPlace := by
  have child : Ancestor (layout false) rootPlace leftPlace :=
    parent_implies_ancestor ⟨by simp [layout], by simp [layout], 0, by simp [layout, path, rootPlace, leftPlace]⟩
  exact ⟨same_place_implies_overlap _ _, ancestor_implies_overlap child,
    Or.inr (Or.inr child), known_disjoint_siblings_do_not_overlap pair_siblings⟩

theorem nested_ancestor_witness :
    Ancestor (layout true) rootPlace nestedPlace ∧ Ancestor (layout true) leftPlace nestedPlace ∧
    ¬ Ancestor (layout true) rightPlace nestedPlace ∧ KnownDisjoint (layout true) leftPlace rightPlace := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨by simp [layout], by simp [layout], [0, 0], by simp, by simp [layout, path, rootPlace, nestedPlace, leftPlace, rightPlace]⟩
  · exact ⟨by simp [layout], by simp [layout], [0], by simp, by simp [layout, path, rootPlace, nestedPlace, leftPlace, rightPlace]⟩
  · rintro ⟨_, _, suffix, _, eq⟩
    have bad := congrArg List.head? eq
    simp [layout, path, rootPlace, leftPlace, rightPlace, nestedPlace] at bad
  · apply known_disjoint_siblings_do_not_overlap
    refine ⟨by decide, rootPlace, ?_, ?_⟩
    · exact ⟨by simp [layout], by simp [layout], 0, by simp [layout, path, rootPlace, leftPlace]⟩
    · exact ⟨by simp [layout], by simp [layout], 1, by simp [layout, path, rootPlace, leftPlace, rightPlace]⟩

theorem local_dependency_is_visible_from_root_subtree :
    LocalDeps (object false true) rootPlace = ∅ ∧
    LocalDeps (object false true) leftPlace = {childAtom} ∧
    LocalDeps (object false true) rightPlace = ∅ ∧
    childAtom ∈ SubtreeDeps (object false true) rootPlace ∧
    childAtom ∈ SubtreeDeps (object false true) leftPlace ∧
    childAtom ∉ SubtreeDeps (object false true) rightPlace := by
  have localDep : childAtom ∈ LocalDeps (object false true) leftPlace := by
    simp [LocalDeps, object, node]
  refine ⟨by simp [LocalDeps, object, node, rootPlace, leftPlace],
    by simp [LocalDeps, object, node], by simp [LocalDeps, object, node, rightPlace, leftPlace], ?_, ?_, ?_⟩
  · exact ancestor_subtree_deps_subset (root_contains_every_place (tree_wellFormed false) (by simp [layout]))
      (local_deps_subset_subtree_deps (by simp [object, layout]) localDep)
  · exact local_deps_subset_subtree_deps (by simp [object, layout]) localDep
  · intro dep
    rcases disjoint_sibling_dependency_not_owned_by_other_sibling pair_siblings dep with ⟨q, _, different, _, owned⟩
    simp [LocalDeps, object, node, different] at owned

private theorem child_erases_to_root (n dep : Bool) : eraseFact (fixture n dep) childAtom = rootAtom := by
  classical
  simp only [eraseFact, childAtom]
  split
  · rfl
  · rename_i missing
    exfalso; apply missing
    refine ⟨location, by simp [fixture], ?_, rfl⟩
    cases n <;> simp [fixture, object, layout]

theorem structural_dependency_is_retained_by_erasure :
    ∃ value, (eraseToF0 (fixture false true)).packages packageId = some value ∧
      rootAtom ∈ value.dependencies := by
  obtain ⟨value, present, deps⟩ := erase_installed_package_present
    (s := fixture false true) (l := location) (by simp [fixture])
  have dep := erase_dependencies_are_conservative
    (s := fixture false true) (l := location) (by simp [fixture])
    local_dependency_is_visible_from_root_subtree.2.2.2.1
  rw [child_erases_to_root] at dep
  exact ⟨value, present, deps ▸ dep⟩

theorem child_histories_survive_flat_erasure :
    (⟨1⟩ : ValueFactId) ∈ (eraseToF0 (fixture false true)).usedValueFacts ∧
    (⟨1⟩ : IncarnationId) ∈ (eraseToF0 (fixture false true)).usedIncarnations ∧
    ¬ F0.FreshValueFact (eraseToF0 (fixture false true)) ⟨1⟩ := by
  have fact := simple_pair_is_wellFormed.valueFactsRecorded location leftPlace
    ⟨by simp [fixture], by simp [fixture, object, layout]⟩
  have inc := simple_pair_is_wellFormed.incarnationsRecorded location leftPlace
    ⟨by simp [fixture], by simp [fixture, object, layout]⟩
  exact ⟨fact, inc, fun fresh => fresh fact⟩

/-- A two-edge malformed parent graph cannot be realized by semantic paths. -/
private def cyclicParentGraph (p q : PlaceId) : Prop :=
  (p = leftPlace ∧ q = rightPlace) ∨ (p = rightPlace ∧ q = leftPlace)

theorem cyclic_structure_is_rejected :
    cyclicParentGraph leftPlace rightPlace ∧ cyclicParentGraph rightPlace leftPlace ∧
    ¬ ∃ l : StructuralLayout, Parent l leftPlace rightPlace ∧ Parent l rightPlace leftPlace := by
  refine ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨l, forward, backward⟩
  have a := parent_increases_depth forward
  have b := parent_increases_depth backward
  omega

theorem duplicate_parent_is_rejected {l : StructuralLayout} (wf : TreeWellFormed l)
    {a b c : PlaceId} (different : a ≠ b) : ¬ (Parent l a c ∧ Parent l b c) :=
  fun h => different (parent_unique wf h.1 h.2)

private def duplicateParentLayout : StructuralLayout :=
  {layout true with path := fun p => if p = rightPlace then [0] else path p}

theorem concrete_duplicate_parent_is_rejected :
    Parent duplicateParentLayout leftPlace nestedPlace ∧
    Parent duplicateParentLayout rightPlace nestedPlace ∧ ¬ TreeWellFormed duplicateParentLayout := by
  have left : Parent duplicateParentLayout leftPlace nestedPlace :=
    ⟨by simp [duplicateParentLayout, layout], by simp [duplicateParentLayout, layout], 0,
      by simp [duplicateParentLayout, path, rootPlace, leftPlace, rightPlace, nestedPlace]⟩
  have right : Parent duplicateParentLayout rightPlace nestedPlace :=
    ⟨by simp [duplicateParentLayout, layout], by simp [duplicateParentLayout, layout], 0,
      by simp [duplicateParentLayout, path, rootPlace, leftPlace, rightPlace, nestedPlace]⟩
  exact ⟨left, right, fun wf => duplicate_parent_is_rejected wf (by decide) ⟨left, right⟩⟩

private def changedNode (change : PlaceId → StructuralNodeState) : State :=
  {fixture false false with root := fun _ => {object false false with node := change}}
private def duplicateFact : State := changedNode (fun p =>
  if p = leftPlace then {node false p with currentFact := ⟨0⟩} else node false p)
private def duplicateIncarnation : State := changedNode (fun p =>
  if p = leftPlace then {node false p with incarnation := ⟨0⟩} else node false p)
private def staleDependency : State :=
  {changedNode (fun p =>
    if p = leftPlace then {node false p with localDeps := {.valueFact leftPlace ⟨99⟩}} else node false p) with
    usedValueFacts := insert ⟨99⟩ (fixture false false).usedValueFacts}

private theorem changed_live (change : PlaceId → StructuralNodeState) (p : PlaceId)
    (tracked : p ∈ (layout false).places) : LiveNode (changedNode change) location p :=
  ⟨by simp [changedNode, fixture], tracked⟩

theorem duplicate_root_child_fact_is_rejected : ¬ WellFormed duplicateFact := by
  intro wf
  have same := wf.currentFactsUnique location rootPlace location leftPlace
    (changed_live _ rootPlace (by simp [layout])) (changed_live _ leftPlace (by simp [layout]))
    (by simp [duplicateFact, changedNode, fixture, object, node, rootPlace, leftPlace])
  have eq := same.2
  simp [rootPlace, leftPlace] at eq

theorem duplicate_structural_incarnation_is_rejected : ¬ WellFormed duplicateIncarnation := by
  intro wf
  have same := wf.incarnationsUnique location rootPlace location leftPlace
    (changed_live _ rootPlace (by simp [layout])) (changed_live _ leftPlace (by simp [layout]))
    (by simp [duplicateIncarnation, changedNode, fixture, object, node, rootPlace, leftPlace])
  have eq := same.2
  simp [rootPlace, leftPlace] at eq

theorem stale_structural_dependency_is_rejected : ¬ WellFormed staleDependency := by
  intro wf
  have live := wf.localDependenciesValid location leftPlace (changed_live _ leftPlace (by simp [layout]))
    (.valueFact leftPlace ⟨99⟩) (by simp [LocalDeps, staleDependency, changedNode])
  rcases live with ⟨l, _, _, bad⟩
  simp [staleDependency, changedNode, node, leftPlace] at bad

theorem recorded_stale_fact_is_not_live :
    (⟨99⟩ : ValueFactId) ∈ staleDependency.usedValueFacts ∧
    Fact.valueFact leftPlace ⟨99⟩ ∉ StructuralLiveFacts staleDependency ∧ ¬ WellFormed staleDependency := by
  refine ⟨by simp [staleDependency], ?_, stale_structural_dependency_is_rejected⟩
  rintro ⟨l, _, _, bad⟩
  simp [staleDependency, changedNode, node, leftPlace] at bad

/-- Deliberately omit all dependency obligations from the flat package table. -/
private def brokenDependencyErasure (s : State) : F0.State :=
  {eraseToF0 s with packages := fun _ => some ⟨∅, false⟩}

private theorem broken_erasure_wellFormed : F0.WellFormed (brokenDependencyErasure (fixture false true)) := by
  have wf := simple_pair_erases_to_wellFormed_f0
  refine ⟨wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique, ?_, wf.domainsValid,
    ?_, wf.valueFactsRecorded, wf.incarnationsRecorded, wf.domainCarrierCoherent⟩
  · intro pkg _; exact ⟨⟨∅, false⟩, rfl⟩
  · intro pkg value _ present fact dep
    have same : value = ⟨∅, false⟩ := (Option.some.inj present).symm
    simp [same] at dep

theorem broken_erasure_loses_child_dependency_obligation :
    WellFormed (fixture false true) ∧
    F0.WellFormed (brokenDependencyErasure (fixture false true)) ∧
    childAtom ∈ LocalDeps (object false true) leftPlace ∧
    (∃ value, (eraseToF0 (fixture false true)).packages packageId = some value ∧ rootAtom ∈ value.dependencies) ∧
    (brokenDependencyErasure (fixture false true)).packages packageId = some ⟨∅, false⟩ ∧
    rootAtom ∉ (∅ : Finset Fact) :=
  ⟨simple_pair_is_wellFormed, broken_erasure_wellFormed,
    by simp [LocalDeps, object, node], structural_dependency_is_retained_by_erasure, rfl, by simp⟩

end
end NewLang.F1.Counterexample.Structural
