import NewLang.F2.Reachability
import Mathlib.Data.Finset.Card

namespace NewLang.F2
open F0
noncomputable section

def breakEdges (k : Loop) := k.edges.filter (fun i => i.isBreak = true)
/-- Finite static exit-index set, not enumeration of all runtime result IDs. -/
def NormalResult (k : Loop) (r : ExitState) : Prop :=
  ∃ s, Reachable k s ∧ ∃ i, Break k i s r

theorem break_edges_finite (k : Loop) : (breakEdges k).card ≤ k.edges.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem break_is_normal_exit {k i s r} (reached : Reachable k s) (step : Break k i s r) : NormalResult k r :=
  ⟨s,reached,i,step⟩

theorem continue_excludes_break_return {k s t i} (step : Continue k i s t) :
    (∀ r, ¬ Break k i s r) ∧ (∀ r, ¬ Return k i s r) := by
  have cls := step.classification
  cases i <;> simp [Edge.isContinue] at cls
  case «continue» n =>
    constructor
    · intro r br; have cls := br.classification; simp [Edge.isBreak] at cls
    · intro r rt; rcases rt.classification with ⟨j,eq⟩; cases eq

theorem break_excludes_header {k i s r} (step : Break k i s r) : ∀ t, ¬ Continue k i s t := by
  intro t cont; exact (continue_excludes_break_return cont).1 r step

theorem return_excludes_header_and_break {k i s r} (step : Return k i s r) :
    (∀ t, ¬ Continue k i s t) ∧ (∀ q, ¬ Break k i s q) := by
  rcases step.classification with ⟨j,rfl⟩
  constructor
  · intro t ct; have cls := ct.classification; simp [Edge.isContinue] at cls
  · intro q br; have cls := br.classification; simp [Edge.isBreak] at cls

theorem zero_break_has_no_normal_result {k} (zero : breakEdges k = ∅) : ∀ r, ¬ NormalResult k r := by
  rintro r ⟨s,_,i,step⟩
  have member : i ∈ breakEdges k := Finset.mem_filter.mpr ⟨step.supplied,step.classification⟩
  rw [zero] at member; exact Finset.notMem_empty _ member

/-- Common finite-exit exact layer. No dynamic result-identity equality premise,
and no requirement to restore entry availability. Copy/non-Copy are separate
static exit slices, never inferred from a package ID. -/
structure ExitSummary where
  type : TypeId
  copy : Bool
  availability : Availability
  origins : May PackageId
  dependencies : May Dependency
  currentFacts : May ValueFactId

def RepresentsExit (r : ExitState) (h : ExitSummary) : Prop :=
  ExitWellFormed r ∧ r.result.type = h.type ∧ r.copy = h.copy ∧
  r.outerAvailability = h.availability ∧ h.origins.Contains r.result.identity ∧
  (∀ d ∈ exitDependencies r, h.dependencies.Contains d) ∧ h.currentFacts.Contains r.currentFact

/-- Sound break analysis starts from the established cyclic H, not first entry. -/
def BreakBound (k : Loop) (h : AbstractHeaderState) (out : ExitSummary) : Prop :=
  ∀ s, Represents s h → ∀ i r, Break k i s r → RepresentsExit r out

theorem reachable_break_summary_sound {k h out r} (pf : PostFixpoint k h) (bound : BreakBound k h out)
    (normal : NormalResult k r) : RepresentsExit r out := by
  rcases normal with ⟨s,reached,i,step⟩; exact bound s (post_fixpoint_sound pf reached) i r step

theorem break_types_availability_agree {a b out} (left : RepresentsExit a out) (right : RepresentsExit b out) :
    a.result.type = b.result.type ∧ a.outerAvailability = b.outerAvailability :=
  ⟨left.2.1.trans right.2.1.symm,left.2.2.2.1.trans right.2.2.2.1.symm⟩

theorem break_runtime_affine_unique {r out} (rep : RepresentsExit r out) (nonCopy : r.copy = false) :
    r.carriers = {r.result.identity} := rep.1.affine nonCopy

/-- Each statically supplied break edge is summarized independently. A finite
join covers those summaries; it need not enumerate dynamic package identities. -/
def ExitIncluded (a b : ExitSummary) : Prop :=
  a.type = b.type ∧ a.copy = b.copy ∧ a.availability = b.availability ∧
  May.Included a.origins b.origins ∧ May.Included a.dependencies b.dependencies ∧
  May.Included a.currentFacts b.currentFacts

theorem exit_representation_monotone {r a b} (rep : RepresentsExit r a) (inc : ExitIncluded a b) :
    RepresentsExit r b :=
  ⟨rep.1,rep.2.1.trans inc.1,rep.2.2.1.trans inc.2.1,
    rep.2.2.2.1.trans inc.2.2.1,inc.2.2.2.1 _ rep.2.2.2.2.1,
    fun d member => inc.2.2.2.2.1 d (rep.2.2.2.2.2.1 d member),
    inc.2.2.2.2.2 _ rep.2.2.2.2.2.2⟩

def IndexedBreakBound (k : Loop) (h : AbstractHeaderState) (summaries : Edge → ExitSummary) : Prop :=
  ∀ s, Represents s h → ∀ i r, Break k i s r → RepresentsExit r (summaries i)

def FiniteBreakJoin (k : Loop) (summaries : Edge → ExitSummary) (out : ExitSummary) : Prop :=
  ∀ i ∈ breakEdges k, ExitIncluded (summaries i) out

theorem finite_break_join_sound {k h summaries out r} (pf : PostFixpoint k h)
    (indexed : IndexedBreakBound k h summaries) (join : FiniteBreakJoin k summaries out)
    (normal : NormalResult k r) : RepresentsExit r out := by
  rcases normal with ⟨s,reached,i,step⟩
  have edge : i ∈ breakEdges k := Finset.mem_filter.mpr ⟨step.supplied,step.classification⟩
  exact exit_representation_monotone (indexed s (post_fixpoint_sound pf reached) i r step) (join i edge)

end
end NewLang.F2
