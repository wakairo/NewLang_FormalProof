import NewLang.F0.WellFormed

/-! Finite semantic paths, not field offsets or source projection syntax. -/
namespace NewLang.F1
open F0

structure StructuralLayout where
  places : Finset PlaceId
  root : PlaceId
  path : PlaceId → List Nat

/-- Paths are root-relative semantic coordinates. Only tracked places matter. -/
structure TreeWellFormed (l : StructuralLayout) : Prop where
  root_tracked : l.root ∈ l.places
  root_path : l.path l.root = []
  paths_unique : ∀ p ∈ l.places, ∀ q ∈ l.places, l.path p = l.path q → p = q
  parent_closed : ∀ p ∈ l.places, p ≠ l.root →
    ∃ q ∈ l.places, ∃ label, l.path p = l.path q ++ [label]

inductive StructuralRole where
  | root
  | fixedSubobject
  deriving DecidableEq, Repr

def role (l : StructuralLayout) (p : PlaceId) : StructuralRole :=
  if p = l.root then .root else .fixedSubobject

def Parent (l : StructuralLayout) (p q : PlaceId) : Prop :=
  p ∈ l.places ∧ q ∈ l.places ∧ ∃ label, l.path q = l.path p ++ [label]

def Ancestor (l : StructuralLayout) (p q : PlaceId) : Prop :=
  p ∈ l.places ∧ q ∈ l.places ∧ ∃ suffix, suffix ≠ [] ∧ l.path q = l.path p ++ suffix

def Descendant (l : StructuralLayout) (q p : PlaceId) : Prop := Ancestor l p q

def Below (l : StructuralLayout) (p q : PlaceId) : Prop := p = q ∨ Ancestor l p q

def Siblings (l : StructuralLayout) (a b : PlaceId) : Prop :=
  a ≠ b ∧ ∃ p, Parent l p a ∧ Parent l p b

def StructuralOverlap (l : StructuralLayout) (p q : PlaceId) : Prop :=
  p = q ∨ Ancestor l p q ∨ Ancestor l q p

def KnownDisjoint (l : StructuralLayout) (p q : PlaceId) : Prop :=
  ¬ StructuralOverlap l p q

theorem parent_increases_depth {l : StructuralLayout} {p q : PlaceId} (h : Parent l p q) :
    (l.path p).length < (l.path q).length := by
  rcases h with ⟨_, _, label, eq⟩; simp [eq]

theorem structural_root_has_no_parent {l : StructuralLayout} (wf : TreeWellFormed l) (p : PlaceId) :
    ¬ Parent l p l.root := by
  intro h; have less := parent_increases_depth h; rw [wf.root_path] at less; simp at less

theorem structural_nonroot_has_parent {l : StructuralLayout} (wf : TreeWellFormed l)
    {p : PlaceId} (tracked : p ∈ l.places) (nonroot : p ≠ l.root) : ∃ q, Parent l q p := by
  rcases wf.parent_closed p tracked nonroot with ⟨q, qt, label, eq⟩
  exact ⟨q, qt, tracked, label, eq⟩

theorem parent_unique {l : StructuralLayout} (wf : TreeWellFormed l) {p q c : PlaceId}
    (a : Parent l p c) (b : Parent l q c) : p = q := by
  rcases a with ⟨pt, _, i, a⟩; rcases b with ⟨qt, _, j, b⟩
  apply wf.paths_unique p pt q qt
  have eq := congrArg List.dropLast (a.symm.trans b)
  simpa using eq

theorem parent_implies_ancestor {l : StructuralLayout} {p q : PlaceId} (h : Parent l p q) :
    Ancestor l p q := by
  rcases h with ⟨pt, qt, label, eq⟩; exact ⟨pt, qt, [label], by simp, eq⟩

theorem ancestor_increases_depth {l : StructuralLayout} {p q : PlaceId} (h : Ancestor l p q) :
    (l.path p).length < (l.path q).length := by
  rcases h with ⟨_, _, suffix, nonempty, eq⟩
  have positive : 0 < suffix.length := by cases suffix <;> simp_all
  simp only [eq, List.length_append]; omega

theorem ancestor_irreflexive (l : StructuralLayout) (p : PlaceId) : ¬ Ancestor l p p :=
  fun h => Nat.lt_irrefl _ (ancestor_increases_depth h)

theorem ancestor_transitive {l : StructuralLayout} {p q r : PlaceId}
    (a : Ancestor l p q) (b : Ancestor l q r) : Ancestor l p r := by
  rcases a with ⟨pt, _, s, ne, a⟩; rcases b with ⟨_, rt, t, _, b⟩
  exact ⟨pt, rt, s ++ t, by cases s <;> simp_all, by rw [b, a, List.append_assoc]⟩

theorem below_transitive {l : StructuralLayout} {p q r : PlaceId}
    (a : Below l p q) (b : Below l q r) : Below l p r := by
  rcases a with rfl | a; exact b
  rcases b with rfl | b; exact Or.inr a
  exact Or.inr (ancestor_transitive a b)

theorem siblings_are_not_ancestors {l : StructuralLayout} {a b : PlaceId} (h : Siblings l a b) :
    ¬ Ancestor l a b ∧ ¬ Ancestor l b a := by
  rcases h with ⟨_, p, ⟨_, _, i, ai⟩, ⟨_, _, j, bj⟩⟩
  have equal : (l.path a).length = (l.path b).length := by simp [ai, bj]
  constructor <;> intro anc <;> have less := ancestor_increases_depth anc <;> omega

theorem known_disjoint_siblings_do_not_overlap {l : StructuralLayout} {a b : PlaceId}
    (h : Siblings l a b) : KnownDisjoint l a b := by
  rcases siblings_are_not_ancestors h with ⟨left, right⟩
  rintro (eq | anc | anc); exact h.1 eq; exact left anc; exact right anc

theorem ancestor_implies_overlap {l : StructuralLayout} {p q : PlaceId} (h : Ancestor l p q) :
    StructuralOverlap l p q := Or.inr (Or.inl h)

theorem same_place_implies_overlap (l : StructuralLayout) (p : PlaceId) :
    StructuralOverlap l p p := Or.inl rfl

theorem root_contains_every_place {l : StructuralLayout} (wf : TreeWellFormed l)
    {p : PlaceId} (tracked : p ∈ l.places) : Below l l.root p := by
  by_cases same : l.root = p
  · exact Or.inl same
  · refine Or.inr ⟨wf.root_tracked, tracked, l.path p, ?_, ?_⟩
    · intro empty; exact same (wf.paths_unique _ wf.root_tracked _ tracked (wf.root_path.trans empty.symm))
    · simp [wf.root_path]

end NewLang.F1
