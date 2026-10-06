import NewLang.F2.Counterexample.Fixture

namespace NewLang.F2.Counterexample
open F0
noncomputable section

/-- No affine loop parameter: the outer Copy component still changes cyclically. -/
theorem pure_copy_cyclic_sound {edges t} (trace : Trace (cyclic false) (entry false) edges t) :
    Represents t (finiteHeader false) ∧ t.parameter = none := by
  have rep := arbitrary_finite_continue_sound (cyclic_postFixpoint false) trace
  refine ⟨rep,?_⟩
  have types := rep.1.types
  cases eq : t.parameter <;> simp [finiteHeader,sig,eq] at types ⊢

def carryLoop : Loop :=
  ⟨sig true,entry true,{.continue 0},fun i s o => match i,o with
    | .continue 0,.continue t => t = unchanged s
    | _,_ => False⟩

theorem unchanged_continue {s} (wf : HeaderWellFormed (sig true) s) :
    Continue carryLoop (.continue 0) s (unchanged s) :=
  ⟨by simp [carryLoop],trivial,rfl,wf,unchanged_wellFormed wf,unchanged_frame s⟩

theorem unchanged_postFixpoint : PostFixpoint carryLoop (finiteHeader true) := by
  refine ⟨rfl,entry_represented true,?_⟩
  intro s rep i t step
  have supplied := step.supplied
  have eqi : i = .continue 0 := by simpa [carryLoop] using supplied
  subst i
  have eq : t = unchanged s := step.body
  subst t
  exact ⟨unchanged_wellFormed rep.1,rep.2⟩

theorem unchanged_symbolic_affine_carry :
    Continue carryLoop (.continue 0) (entry true) (unchanged (entry true)) ∧
    (unchanged (entry true)).parameter = (entry true).parameter ∧
    (unchanged (entry true)).binding ≠ (entry true).binding :=
  ⟨unchanged_continue (entry_wellFormed true),rfl,
    (Continue.next_binding_fresh (unchanged_continue (entry_wellFormed true))).2⟩

theorem hidden_dependency_recurs_without_erasure {s edges}
    (trace : Trace carryLoop (entry true) edges s) :
    s.parameter = (entry true).parameter ∧ dep 0 ∈ survivingDependencies s := by
  have preserve : ∀ t u es, Trace carryLoop t es u → u.parameter = t.parameter := by
    intro t u es tr
    induction tr with
    | nil => rfl
    | cons step _ ih =>
      have eqi := step.supplied
      simp only [carryLoop,Finset.mem_singleton] at eqi
      have body := step.body
      rw [eqi] at body
      have eq : _ = unchanged _ := body
      exact ih.trans (by simpa [unchanged] using congrArg ConcreteHeaderState.parameter eq)
  have eq := preserve _ _ _ trace
  refine ⟨eq,?_⟩
  apply Finset.mem_union_left
  simp [carriedDependencies,eq,entry]

theorem transformed_affine_carry :
    Continue (cyclic true) (.continue 0) (entry true) (advance (entry true) 0) ∧
    (advance (entry true) 0).parameter.map Package.type = (entry true).parameter.map Package.type ∧
    (advance (entry true) 0).parameter.map Package.identity ≠ (entry true).parameter.map Package.identity := by
  refine ⟨cyclic_continue (entry_wellFormed true) 0,?_,?_⟩
  · rfl
  · simp [advance,advancedParameter,entry,nextPackage]

theorem two_edges_distinct_alternatives :
    Continue (cyclic true) (.continue 0) (entry true) (advance (entry true) 0) ∧
    Continue (cyclic true) (.continue 1) (entry true) (advance (entry true) 1) ∧
    survivingDependencies (advance (entry true) 0) ≠ survivingDependencies (advance (entry true) 1) ∧
    (advance (entry true) 0).currentFact ≠ (advance (entry true) 1).currentFact ∧
    (advance (entry true) 0).parameter.map Package.identity ≠ (advance (entry true) 1).parameter.map Package.identity := by
  refine ⟨cyclic_continue (entry_wellFormed true) 0,cyclic_continue (entry_wellFormed true) 1,?_,?_,?_⟩
  · rw [advance_dependencies,advance_dependencies]; decide
  · simp [advance,nextFact,entry]
  · simp [advance,advancedParameter,nextPackage,entry]

theorem all_continue_sequences_exact_availability {s edges}
    (trace : Trace (cyclic true) (entry true) edges s) : s.outerAvailability = .available :=
  (arbitrary_finite_continue_sound (cyclic_postFixpoint true) trace).1.availability

def firstOnly : AbstractHeaderState :=
  {finiteHeader true with currentFacts := .known {⟨0⟩}}

theorem first_entry_only_is_not_inductive : Represents (entry true) firstOnly ∧
    ¬ Represents (advance (entry true) 0) firstOnly ∧ ¬ PostFixpoint (cyclic true) firstOnly := by
  have start : Represents (entry true) firstOnly :=
    ⟨(entry_represented true).1,(entry_represented true).2.1,(entry_represented true).2.2.1,by simp [firstOnly,entry,May.Contains]⟩
  have absent : ¬ Represents (advance (entry true) 0) firstOnly := by
    intro rep
    have facts := rep.2.2.2
    simp [firstOnly,May.Contains,advance,nextFact,entry] at facts
  refine ⟨start,absent,?_⟩
  intro pf; exact absent (pf.2.2 _ start _ _ (cyclic_continue (entry_wellFormed true) 0))

theorem underapproximation_is_not_sound :
    ¬ (∀ s, Reachable (cyclic true) s → Represents s firstOnly) := by
  intro claimed
  exact first_entry_only_is_not_inductive.2.1
    (claimed _ (.backedge .entry (cyclic_continue (entry_wellFormed true) 0)))

def onlyLeft : AbstractHeaderState := {finiteHeader true with dependencies := .known {dep 0}}

theorem omitted_continue_edge_breaks_closure :
    Represents (entry true) onlyLeft ∧
    (∀ s, Represents s onlyLeft → ∀ t, Continue (cyclic true) (.continue 0) s t → Represents t onlyLeft) ∧
    ¬ Closed (cyclic true) onlyLeft := by
  have start : Represents (entry true) onlyLeft := by
    refine ⟨(entry_represented true).1,by intros; trivial,?_,trivial⟩
    simp [survivingDependencies,carriedDependencies,entry,onlyLeft,May.Contains]
  refine ⟨start,?_,?_⟩
  · intro s rep t step
    have eq : t = advance s 0 := step.body
    subst t
    refine ⟨advance_wellFormed rep.1 0,by intros; trivial,?_,trivial⟩
    rw [advance_dependencies]; intro d mem
    simpa [onlyLeft,May.Contains] using mem
  · intro closed
    have rep := closed _ start _ _ (cyclic_continue (entry_wellFormed true) 1)
    have includes := rep.2.2.1 (dep 1) (by rw [advance_dependencies]; simp)
    simp [onlyLeft,May.Contains,dep] at includes

def wideHeader : AbstractHeaderState := {finiteHeader true with dependencies := .unknown}
def extraState : ConcreteHeaderState :=
  {entry true with currentDependencies := {.externalFact (.valueFact ⟨0⟩ ⟨0⟩)}}

theorem larger_header_is_inductive : PostFixpoint (cyclic true) wideHeader := by
  refine ⟨rfl,⟨entry_wellFormed true,by intros; trivial,by intros; trivial,trivial⟩,?_⟩
  intro s rep i t step
  exact ⟨step.after,by intros; trivial,by intros; trivial,trivial⟩

theorem larger_than_reachable_is_still_sound : Represents extraState wideHeader ∧
    ¬ Reachable (cyclic true) extraState ∧
    (∀ s, Reachable (cyclic true) s → Represents s wideHeader) := by
  have wf : HeaderWellFormed (sig true) extraState := by
    constructor <;> simp [extraState,entry,sig,expectedCarriers,ScopeClosed,
      survivingDependencies,carriedDependencies,FactLive,dep]
  refine ⟨⟨wf,by intros; trivial,by intros; trivial,trivial⟩,?_,any_inductive_overapproximation_suffices larger_header_is_inductive⟩
  intro reached
  have rep := post_fixpoint_sound (cyclic_postFixpoint true) reached
  have blocker := rep.2.2.1 (.externalFact (.valueFact ⟨0⟩ ⟨0⟩))
    (by simp [extraState,survivingDependencies,carriedDependencies])
  simp [finiteHeader,May.Contains,dep] at blocker

/-- Incorrectly retaining only one dependency alternative permits an unsafe
invalidation, even though the omitted blocker occurs in a legal backedge. -/
theorem dropped_join_blocker_looks_safe_but_conflicts :
    SafeInvalidation onlyLeft {dep 1} ∧
    ConcreteConflict (advance (entry true) 1) {dep 1} ∧
    ¬ May.Included (May.join (.known {dep 0}) (.known {dep 1})) onlyLeft.dependencies := by
  refine ⟨?_,⟨dep 1,by rw [advance_dependencies]; simp,by simp⟩,?_⟩
  · intro d member; have eq := Finset.mem_singleton.mp member; subst d
    simp [onlyLeft,May.Contains,dep]
  · intro included
    have contradiction := included (dep 1) (May.join_right _ _ _ (by simp [May.Contains]))
    simp [onlyLeft,May.Contains,dep] at contradiction

theorem unknown_retains_concrete_blocker : Represents (entry true) wideHeader ∧
    ¬ SafeInvalidation wideHeader {dep 0} :=
  ⟨larger_header_is_inductive.2.1,unknown_is_not_dependency_free _ _ _ _⟩

def run (s : ConcreteHeaderState) : List (Fin 2) → ConcreteHeaderState
  | [] => s
  | i :: is => run (advance s i) is

theorem every_finite_edge_sequence_has_trace {affine s} (wf : HeaderWellFormed (sig affine) s)
    (indices : List (Fin 2)) :
    Trace (cyclic affine) s (indices.map Edge.continue) (run s indices) := by
  induction indices generalizing s with
  | nil => exact .nil s
  | cons i is ih => exact .cons (cyclic_continue wf i) (ih (advance_wellFormed wf i))

theorem every_finite_edge_sequence_is_sound (affine : Bool) (indices : List (Fin 2)) :
    Represents (run (entry affine) indices) (finiteHeader affine) :=
  arbitrary_finite_continue_sound (cyclic_postFixpoint affine)
    (every_finite_edge_sequence_has_trace (entry_wellFormed affine) indices)

end
end NewLang.F2.Counterexample
