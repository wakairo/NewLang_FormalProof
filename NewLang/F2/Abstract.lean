import NewLang.F2.Model

namespace NewLang.F2
open F0
noncomputable section

/-- A proof abstraction; Unknown includes all possibilities, never an empty set. -/
inductive May (α : Type) where
  | known : Finset α → May α
  | unknown : May α
namespace May
variable {α : Type} [DecidableEq α]
def Contains (a : May α) (x : α) : Prop := match a with
  | .known xs => x ∈ xs | .unknown => True
def Included (a b : May α) : Prop := ∀ x, a.Contains x → b.Contains x
def join : May α → May α → May α
  | .known a,.known b => .known (a ∪ b)
  | _,_ => .unknown

theorem join_left (a b : May α) : Included a (join a b) := by
  intro x member; cases a <;> cases b <;> simp_all [Contains,join]
theorem join_right (a b : May α) : Included b (join a b) := by
  intro x member; cases a <;> cases b <;> simp_all [Contains,join]
omit [DecidableEq α] in
theorem unknown_contains (x : α) : Contains (.unknown : May α) x := trivial
end May

/-- Binding/package IDs remain different. A symbolic affine slot can represent
unbounded different packages while exact concrete carrier uniqueness is retained. -/
structure AbstractHeaderState where
  signature : Signature
  origins : May PackageId
  dependencies : May Dependency
  currentFacts : May ValueFactId

def Represents (s : ConcreteHeaderState) (h : AbstractHeaderState) : Prop :=
  HeaderWellFormed h.signature s ∧
  (∀ p, s.parameter = some p → h.origins.Contains p.identity) ∧
  (∀ d ∈ survivingDependencies s, h.dependencies.Contains d) ∧
  h.currentFacts.Contains s.currentFact

/-- Exact signature/availability/scope/carriers are never weakened by widening. -/
def Widen (a b : AbstractHeaderState) : Prop :=
  b.signature = a.signature ∧ May.Included a.origins b.origins ∧
  May.Included a.dependencies b.dependencies ∧ May.Included a.currentFacts b.currentFacts

theorem represents_widen {s a b} (rep : Represents s a) (wide : Widen a b) : Represents s b :=
  ⟨wide.1 ▸ rep.1,fun p eq => wide.2.1 _ (rep.2.1 p eq),
    fun d member => wide.2.2.1 _ (rep.2.2.1 d member),wide.2.2.2 _ rep.2.2.2⟩

def SafeInvalidation (h : AbstractHeaderState) (killed : Finset Dependency) : Prop :=
  ∀ d ∈ killed, ¬ h.dependencies.Contains d
def ConcreteConflict (s : ConcreteHeaderState) (killed : Finset Dependency) : Prop :=
  ∃ d ∈ survivingDependencies s, d ∈ killed

theorem represented_safety {s h killed} (rep : Represents s h) (safe : SafeInvalidation h killed) :
    ¬ ConcreteConflict s killed := by
  rintro ⟨d,carried,dead⟩; exact safe d dead (rep.2.2.1 d carried)

theorem widening_never_erases_blocker {s a b d} (rep : Represents s a) (wide : Widen a b)
    (dep : d ∈ survivingDependencies s) : b.dependencies.Contains d := wide.2.2.1 d (rep.2.2.1 d dep)

theorem lost_correlation_cannot_justify_invalidation {s a b d} (rep : Represents s a)
    (wide : Widen a b) (dep : d ∈ survivingDependencies s) : ¬ SafeInvalidation b {d} := by
  intro safe; exact safe d (Finset.mem_singleton_self d) (widening_never_erases_blocker rep wide dep)

theorem unknown_is_not_dependency_free (sig : Signature) (orig : May PackageId) (facts : May ValueFactId) (d : Dependency) :
    ¬ SafeInvalidation ⟨sig,orig,.unknown,facts⟩ {d} := by
  intro safe; exact safe d (Finset.mem_singleton_self d) trivial

end
end NewLang.F2
