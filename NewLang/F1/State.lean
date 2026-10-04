import NewLang.F1.Structural
import Mathlib.Data.Finset.Union

namespace NewLang.F1
open F0

/-- One canonical local fragment per tracked place. Payload remains opaque. -/
structure StructuralNodeState where
  incarnation : IncarnationId
  currentFact : ValueFactId
  localDeps : Finset Fact

/-- Root-only metadata is stored once; children have no occupancy/domain copies. -/
structure StructuredRoot where
  layout : StructuralLayout
  node : PlaceId → StructuralNodeState
  package : PackageId
  governing : DomainId
  discardable : Bool

/-- Finite live root support; functions outside support are inactive data. -/
structure State where
  liveRoots : Finset RootLocationId
  root : RootLocationId → StructuredRoot
  loosePackages : Finset PackageId
  looseValues : PackageId → Option ValuePackage
  liveDomains : Finset DomainId
  domainValueCarrier : DomainId → Option DomainValueCarrierId
  usedValueFacts : Finset ValueFactId
  usedIncarnations : Finset IncarnationId

def LocalDeps (r : StructuredRoot) (p : PlaceId) : Finset Fact := (r.node p).localDeps

/-- Derived subtree union; there is no stored parent summary or duplicate package. -/
noncomputable def SubtreeDeps (r : StructuredRoot) (p : PlaceId) : Finset Fact := by
  classical
  exact (r.layout.places.filter (Below r.layout p)).biUnion (LocalDeps r)

def StructuralLiveFacts (s : State) : Set Fact := fun fact => match fact with
  | .valueFact p vf => ∃ l ∈ s.liveRoots, p ∈ (s.root l).layout.places ∧ ((s.root l).node p).currentFact = vf
  | .domainLive d => d ∈ s.liveDomains

theorem local_deps_subset_subtree_deps {r : StructuredRoot} {p : PlaceId}
    (tracked : p ∈ r.layout.places) : LocalDeps r p ⊆ SubtreeDeps r p := by
  classical
  intro f dep
  exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨tracked, Or.inl rfl⟩, dep⟩

theorem ancestor_subtree_deps_subset {r : StructuredRoot} {p q : PlaceId}
    (below : Below r.layout p q) : SubtreeDeps r q ⊆ SubtreeDeps r p := by
  classical
  intro f dep
  rcases Finset.mem_biUnion.mp dep with ⟨n, tracked, owned⟩
  rcases Finset.mem_filter.mp tracked with ⟨nt, nq⟩
  exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_filter.mpr ⟨nt, below_transitive below nq⟩, owned⟩

theorem child_subtree_deps_subset_parent_subtree_deps {r : StructuredRoot} {p q : PlaceId}
    (child : Parent r.layout p q) : SubtreeDeps r q ⊆ SubtreeDeps r p :=
  ancestor_subtree_deps_subset (Or.inr (parent_implies_ancestor child))

/-- Every derived dependency has an actual local owner in the selected subtree. -/
theorem subtree_dependency_has_local_owner {r : StructuredRoot} {p : PlaceId} {f : Fact}
    (dep : f ∈ SubtreeDeps r p) : ∃ q ∈ r.layout.places, Below r.layout p q ∧ f ∈ LocalDeps r q := by
  classical
  rcases Finset.mem_biUnion.mp dep with ⟨q, tracked, owned⟩
  rcases Finset.mem_filter.mp tracked with ⟨qt, below⟩
  exact ⟨q, qt, below, owned⟩

/-- An atom visible at sibling b must be owned somewhere in b's own subtree,
not inherited from a. The same atom can independently be owned on both sides. -/
theorem disjoint_sibling_dependency_not_owned_by_other_sibling {r : StructuredRoot}
    {a b : PlaceId} {f : Fact} (siblings : Siblings r.layout a b) (dep : f ∈ SubtreeDeps r b) :
    ∃ q ∈ r.layout.places, q ≠ a ∧ Below r.layout b q ∧ f ∈ LocalDeps r q := by
  rcases subtree_dependency_has_local_owner dep with ⟨q, qt, below, owned⟩
  refine ⟨q, qt, ?_, below, owned⟩
  intro same; subst q
  rcases below with same | anc
  · exact siblings.1 same.symm
  · exact (siblings_are_not_ancestors siblings).2 anc

end NewLang.F1
