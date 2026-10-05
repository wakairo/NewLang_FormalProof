import NewLang.F1.Erasure

namespace NewLang.F1
open F0
noncomputable section

/-- A place-owned address within the fixed structural model. -/
structure StructuralTarget where
  location : RootLocationId
  place : PlaceId
  deriving DecidableEq

/-- Opaque semantic content is represented by a token, not by an ABI or a type tree.
Dependencies are exact facts; they are never rewritten during value transfer. -/
structure ValueFragment where
  content : Nat
  dependencies : Finset Fact

/-- Value-relative positions contain no source place/incarnation/domain metadata.
Capability bits describe the fixed type at each position, not runtime payload. -/
structure StructuredValue where
  shape : Finset (List Nat)
  fragment : List Nat → ValueFragment
  discardable : List Nat → Bool

def StructuredValue.dependencies (v : StructuredValue) : Finset Fact :=
  v.shape.biUnion (fun k => (v.fragment k).dependencies)

def StructuredValue.summary (v : StructuredValue) : ValuePackage :=
  ⟨v.dependencies, v.discardable []⟩

/-- Conservative extension of the reviewed F1.0 state. Its flat loose table is a
checked summary of the carried structured value; installed fragments use LocalDeps.
The capability map is static type metadata and is preserved by all three operations. -/
structure CurrentState where
  base : State
  content : RootLocationId → PlaceId → Nat
  capability : RootLocationId → PlaceId → Bool
  carried : PackageId → Option StructuredValue

structure CurrentWellFormed (s : CurrentState) : Prop where
  structural : WellFormed s.base
  looseStructured : ∀ pkg ∈ s.base.loosePackages,
    ∃ v, s.carried pkg = some v ∧ s.base.looseValues pkg = some v.summary
  rootCapability : ∀ l ∈ s.base.liveRoots,
    s.capability l (s.base.root l).layout.root = (s.base.root l).discardable

def relativePosition (r : StructuredRoot) (target p : PlaceId) : List Nat :=
  (r.layout.path p).drop (r.layout.path target).length

def subtreePlaces (r : StructuredRoot) (target : PlaceId) : Finset PlaceId := by
  classical
  exact r.layout.places.filter (Below r.layout target)

theorem below_path_decomposition {r : StructuredRoot} {p q : PlaceId}
    (below : Below r.layout p q) :
    r.layout.path q = r.layout.path p ++ relativePosition r p q := by
  rcases below with rfl | ⟨_, _, suffix, _, eq⟩
  · simp [relativePosition]
  · simp [relativePosition, eq]

theorem relative_positions_injective {r : StructuredRoot} (tree : TreeWellFormed r.layout)
    {p a b : PlaceId} (aLive : a ∈ subtreePlaces r p) (bLive : b ∈ subtreePlaces r p)
    (same : relativePosition r p a = relativePosition r p b) : a = b := by
  classical
  rcases Finset.mem_filter.mp aLive with ⟨aTracked, ab⟩
  rcases Finset.mem_filter.mp bLive with ⟨bt, bb⟩
  apply tree.paths_unique a aTracked b bt
  rw [below_path_decomposition ab, below_path_decomposition bb, same]

/-- Extract the complete subtree, preserving the local partition at relative positions.
Inactive coordinates are irrelevant; selection is unique under TreeWellFormed. -/
def extractValue (s : CurrentState) (t : StructuralTarget) : StructuredValue := by
  classical
  let r := s.base.root t.location
  let select := fun k => if h : ∃ q ∈ subtreePlaces r t.place, relativePosition r t.place q = k
    then Classical.choose h else t.place
  exact ⟨(subtreePlaces r t.place).image (relativePosition r t.place),
    fun k => ⟨s.content t.location (select k), LocalDeps r (select k)⟩,
    fun k => s.capability t.location (select k)⟩

theorem extract_value_fragment {s : CurrentState} (wf : CurrentWellFormed s)
    {t : StructuralTarget} (live : t.location ∈ s.base.liveRoots) {q : PlaceId}
    (inside : q ∈ subtreePlaces (s.base.root t.location) t.place) :
    let k := relativePosition (s.base.root t.location) t.place q
    (extractValue s t).fragment k =
      ⟨s.content t.location q, LocalDeps (s.base.root t.location) q⟩ ∧
    (extractValue s t).discardable k = s.capability t.location q := by
  classical
  have found : ∃ p ∈ subtreePlaces (s.base.root t.location) t.place,
      relativePosition (s.base.root t.location) t.place p = relativePosition (s.base.root t.location) t.place q :=
    ⟨q, inside, rfl⟩
  have spec := Classical.choose_spec found
  have same := relative_positions_injective (wf.structural.trees _ live) spec.1 inside spec.2
  simp [extractValue, dite_eq_left found, same]

theorem extract_value_dependencies {s : CurrentState} (wf : CurrentWellFormed s)
    {t : StructuralTarget} (live : t.location ∈ s.base.liveRoots) :
    (extractValue s t).dependencies = SubtreeDeps (s.base.root t.location) t.place := by
  classical
  ext f
  constructor
  · intro dep
    rcases Finset.mem_biUnion.mp dep with ⟨k, kt, dep⟩
    rcases Finset.mem_image.mp kt with ⟨q, qt, rfl⟩
    rw [(extract_value_fragment wf live qt).1] at dep
    exact Finset.mem_biUnion.mpr ⟨q, qt, dep⟩
  · intro dep
    rcases Finset.mem_biUnion.mp dep with ⟨q, qt, dep⟩
    refine Finset.mem_biUnion.mpr ⟨relativePosition _ _ q, Finset.mem_image.mpr ⟨q, qt, rfl⟩, ?_⟩
    rw [(extract_value_fragment wf live qt).1]
    exact dep

/-- Exact shape and type-capability agreement are checked; type checking itself is external. -/
def FitsTarget (s : CurrentState) (t : StructuralTarget) (v : StructuredValue) : Prop :=
  v.shape = (extractValue s t).shape ∧
  ∀ q ∈ subtreePlaces (s.base.root t.location) t.place,
    v.discardable (relativePosition (s.base.root t.location) t.place q) = s.capability t.location q

theorem carried_dependency_survives_erasure {s : CurrentState} (wf : CurrentWellFormed s)
    {pkg : PackageId} (loose : pkg ∈ s.base.loosePackages) {v : StructuredValue}
    (value : s.carried pkg = some v) {f : Fact} (dep : f ∈ v.dependencies) :
    eraseFact s.base f ∈ F0.LiveFacts (eraseToF0 s.base) := by
  rcases wf.looseStructured pkg loose with ⟨actual, eq, summary⟩
  have same : actual = v := Option.some.inj (eq.symm.trans value)
  subst actual
  exact erase_live_fact (wf.structural.looseDependenciesValid pkg loose v.summary summary f dep)


/-- Not just liveness: every carried dependency appears in the actual erased table. -/
theorem carried_structured_dependency_is_retained_by_erasure {s : CurrentState}
    (wf : CurrentWellFormed s) {pkg : PackageId} (loose : pkg ∈ s.base.loosePackages)
    {v : StructuredValue} (value : s.carried pkg = some v) {f : Fact} (dep : f ∈ v.dependencies) :
    ∃ flatValue, (eraseToF0 s.base).packages pkg = some flatValue ∧
      eraseFact s.base f ∈ flatValue.dependencies := by
  classical
  rcases wf.looseStructured pkg loose with ⟨actual,actualEq,data⟩
  have same : actual = v := Option.some.inj (actualEq.symm.trans value)
  subst actual
  have ownersEmpty : installedOwners s.base pkg = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l owner
    rcases Finset.mem_filter.mp owner with ⟨live,packageEq⟩
    exact wf.structural.installedNotLoose l live (packageEq.symm ▸ loose)
  refine ⟨eraseLooseValue s.base v.summary,?_,?_⟩
  · simp [eraseToF0,erasePackages,ownersEmpty,data]
  · exact Finset.mem_image.mpr ⟨f,dep,rfl⟩

end
end NewLang.F1
