import NewLang.F2.Counterexample.Affine

namespace NewLang.F2.Counterexample
open F0
noncomputable section

def exit (copy : Bool) (s : ConcreteHeaderState) (i : Fin 2) : ExitState :=
  ⟨⟨nextPackage s i,if copy then ⟨1⟩ else ⟨0⟩,{dep i}⟩,copy,{nextPackage s i},.consumed,nextFact s i,{dep i}⟩

def withExits (copy : Bool) : Loop :=
  ⟨sig true,entry true,{.continue 0,.continue 1,.break 0,.break 1,.return 0},
    fun i s outcome => match i,outcome with
      | .continue j,.continue t => t = advance s j
      | .break j,.break r => r = exit copy s j
      | .return j,.return r => r = exit copy s j
      | _,_ => False⟩

def zeroBreak : Loop :=
  {withExits false with edges := {.continue 0,.continue 1,.return 0}}

def output (copy : Bool) : ExitSummary :=
  ⟨if copy then ⟨1⟩ else ⟨0⟩,copy,.consumed,.unknown,.known {dep 0,dep 1},.unknown⟩

theorem exit_wellFormed (copy : Bool) (s : ConcreteHeaderState) (i : Fin 2) : ExitWellFormed (exit copy s i) := by
  constructor
  · intro _; rfl
  · simp [ScopeClosed,exitDependencies,exit,dep]

theorem exit_dependencies_live (copy : Bool) (s : ConcreteHeaderState) (i : Fin 2) : ExitFactsLive (sig true) (exit copy s i) := by
  intro d member
  have eq : d = dep i := by simpa [exitDependencies,exit] using member
  subst d
  refine ⟨.domainLive ⟨i.val⟩,rfl,Or.inl ?_⟩
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl|rfl <;> simp [sig]

theorem exits_postFixpoint (copy : Bool) : PostFixpoint (withExits copy) (finiteHeader true) := by
  refine ⟨rfl,entry_represented true,?_⟩
  intro s rep i t step
  have cls := step.classification
  cases i <;> simp [Edge.isContinue] at cls
  case «continue» j =>
    have eq : t = advance s j := step.body
    subst t; exact advanced_represented rep.1 j

theorem exit_represented (copy : Bool) (s : ConcreteHeaderState) (i : Fin 2) : RepresentsExit (exit copy s i) (output copy) := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl|rfl <;>
    refine ⟨exit_wellFormed _ _ _,rfl,rfl,rfl,?_,?_,?_⟩ <;>
    simp [output,exit,exitDependencies,May.Contains]

theorem finite_break_bound (copy : Bool) : BreakBound (withExits copy) (finiteHeader true) (output copy) := by
  intro s _ i r step
  have cls := step.classification
  cases i <;> simp [Edge.isBreak] at cls
  case «break» j =>
    have eq : r = exit copy s j := step.body
    subst r; exact exit_represented copy s j

theorem concrete_break (copy : Bool) (i : Fin 2) : Break (withExits copy) (.break i) (entry true) (exit copy (entry true) i) := by
  have cases : i = 0 ∨ i = 1 := by omega
  refine ⟨?_,rfl,rfl,entry_wellFormed true,exit_wellFormed copy (entry true) i,exit_dependencies_live copy (entry true) i⟩
  rcases cases with rfl|rfl <;> simp [withExits]

theorem finite_copy_break_alternatives :
    NormalResult (withExits true) (exit true (entry true) 0) ∧ NormalResult (withExits true) (exit true (entry true) 1) ∧
    RepresentsExit (exit true (entry true) 0) (output true) ∧ RepresentsExit (exit true (entry true) 1) (output true) :=
  ⟨break_is_normal_exit .entry (concrete_break true 0),break_is_normal_exit .entry (concrete_break true 1),
    reachable_break_summary_sound (exits_postFixpoint true) (finite_break_bound true)
      (break_is_normal_exit .entry (concrete_break true 0)),exit_represented true (entry true) 1⟩

theorem finite_noncopy_break_alternatives :
    NormalResult (withExits false) (exit false (entry true) 0) ∧ NormalResult (withExits false) (exit false (entry true) 1) ∧
    (exit false (entry true) 0).result.type = (exit false (entry true) 1).result.type ∧
    (exit false (entry true) 0).result.identity ≠ (exit false (entry true) 1).result.identity ∧
    (exit false (entry true) 0).outerAvailability ≠ (entry true).outerAvailability := by
  refine ⟨break_is_normal_exit .entry (concrete_break false 0),break_is_normal_exit .entry (concrete_break false 1),rfl,?_,?_⟩
  · simp [exit,nextPackage,entry]
  · decide

theorem break_does_not_feed_header : Break (withExits false) (.break 0) (entry true) (exit false (entry true) 0) ∧
    ∀ t, ¬ Continue (withExits false) (.break 0) (entry true) t :=
  ⟨concrete_break false 0,break_excludes_header (concrete_break false 0)⟩

theorem zero_break_edge_set : breakEdges zeroBreak = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i member
  have pair := Finset.mem_filter.mp member
  have cls := pair.2
  cases i <;> simp [Edge.isBreak] at cls
  case «break» j =>
    have supplied := pair.1
    simp [zeroBreak,withExits] at supplied

theorem zero_break_postFixpoint : PostFixpoint zeroBreak (finiteHeader true) := by
  refine ⟨rfl,entry_represented true,?_⟩
  intro s rep i t step
  have cls := step.classification
  cases i <;> simp [Edge.isContinue] at cls
  case «continue» j =>
    have eq : t = advance s j := step.body
    subst t; exact advanced_represented rep.1 j

theorem zero_break_still_has_continue : Continue zeroBreak (.continue 0) (entry true) (advance (entry true) 0) :=
  ⟨by simp [zeroBreak,withExits],trivial,rfl,entry_wellFormed true,
    advance_wellFormed (entry_wellFormed true) 0,advance_frame _ 0⟩

theorem concrete_return : Return zeroBreak (.return 0) (entry true) (exit false (entry true) 0) :=
  ⟨by simp [zeroBreak,withExits],⟨0,rfl⟩,rfl,entry_wellFormed true,
    exit_wellFormed false (entry true) 0,exit_dependencies_live false (entry true) 0⟩

theorem return_does_not_feed_header : Return zeroBreak (.return 0) (entry true) (exit false (entry true) 0) ∧
    ∀ t, ¬ Continue zeroBreak (.return 0) (entry true) t :=
  ⟨concrete_return,(return_excludes_header_and_break concrete_return).1⟩

theorem return_is_not_a_break_result : Return zeroBreak (.return 0) (entry true) (exit false (entry true) 0) ∧
    ¬ NormalResult zeroBreak (exit false (entry true) 0) :=
  ⟨concrete_return,zero_break_has_no_normal_result zero_break_edge_set _⟩

/-- A deliberately fabricated normal value; no synthetic Unit type is added to
production semantics. No value of any type is a normal result of this kernel. -/
def syntheticNormal : ExitState :=
  ⟨⟨⟨777⟩,⟨777⟩,∅⟩,true,{⟨777⟩},.available,⟨0⟩,∅⟩

theorem zero_break_cannot_synthesize_unit_like_result :
    PostFixpoint zeroBreak (finiteHeader true) ∧
    ¬ NormalResult zeroBreak syntheticNormal ∧ ∀ r, ¬ NormalResult zeroBreak r :=
  ⟨zero_break_postFixpoint,zero_break_has_no_normal_result zero_break_edge_set _,
    zero_break_has_no_normal_result zero_break_edge_set⟩

def edgeSummary (copy : Bool) (i : Edge) : ExitSummary :=
  match i with
  | .break j => ⟨if copy then ⟨1⟩ else ⟨0⟩,copy,.consumed,.unknown,.known {dep j},.unknown⟩
  | _ => output copy

theorem finite_indexed_break_bound (copy : Bool) :
    IndexedBreakBound (withExits copy) (finiteHeader true) (edgeSummary copy) := by
  intro s _ i r step
  have cls := step.classification
  cases i <;> simp [Edge.isBreak] at cls
  case «break» j =>
    have eq : r = exit copy s j := step.body
    subst r
    refine ⟨exit_wellFormed copy s j,rfl,rfl,rfl,?_,?_,?_⟩ <;>
      simp [edgeSummary,exit,exitDependencies,May.Contains]

theorem finite_indexed_join (copy : Bool) :
    FiniteBreakJoin (withExits copy) (edgeSummary copy) (output copy) := by
  intro i member
  have cls : i.isBreak = true := (Finset.mem_filter.mp member).2
  cases i <;> simp [Edge.isBreak] at cls
  case «break» j =>
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl|rfl <;>
      refine ⟨rfl,rfl,rfl,?_,?_,?_⟩ <;> simp [May.Included,May.Contains,edgeSummary,output]

theorem finite_exit_analysis_after_inductive_header {copy r} (normal : NormalResult (withExits copy) r) :
    RepresentsExit r (output copy) :=
  finite_break_join_sound (exits_postFixpoint copy) (finite_indexed_break_bound copy)
    (finite_indexed_join copy) normal

end
end NewLang.F2.Counterexample
