import NewLang.F2.Exit
import Mathlib.Data.Finset.Lattice.Fold

namespace NewLang.F2.Counterexample
open F0
noncomputable section

def dep (i : Fin 2) : Dependency := .externalFact (.domainLive ⟨i.val⟩)
def sig (affine : Bool) : Signature :=
  ⟨if affine then some ⟨0⟩ else none,.available,⟨0⟩,{.domainLive ⟨0⟩,.domainLive ⟨1⟩}⟩
def nextBinding (s : ConcreteHeaderState) : BindingId := ⟨s.usedBindings.sup BindingId.index + 1⟩
def nextPackage (s : ConcreteHeaderState) (i : Fin 2) : PackageId := ⟨s.usedPackages.sup PackageId.index + 1 + i.val⟩
def nextFact (s : ConcreteHeaderState) (i : Fin 2) : ValueFactId := ⟨s.usedFacts.sup ValueFactId.index + 1 + i.val⟩

theorem next_binding_unused (s : ConcreteHeaderState) : nextBinding s ∉ s.usedBindings := by
  intro member
  have bound := Finset.le_sup (f := BindingId.index) member
  simp only [nextBinding] at bound
  omega

theorem next_package_unused (s : ConcreteHeaderState) (i : Fin 2) : nextPackage s i ∉ s.usedPackages := by
  intro member
  have bound := Finset.le_sup (f := PackageId.index) member
  simp only [nextPackage] at bound
  omega

theorem next_fact_unused (s : ConcreteHeaderState) (i : Fin 2) : nextFact s i ∉ s.usedFacts := by
  intro member
  have bound := Finset.le_sup (f := ValueFactId.index) member
  simp only [nextFact] at bound
  omega

def advancedParameter (s : ConcreteHeaderState) (i : Fin 2) :=
  s.parameter.map (fun p => ({identity := nextPackage s i, type := p.type, dependencies := {dep i}} : Package))

def advance (s : ConcreteHeaderState) (i : Fin 2) : ConcreteHeaderState :=
  let p := advancedParameter s i
  { binding := nextBinding s, parameter := p,
    carriers := (p.map (fun p => ({(nextBinding s,p.identity)} : Finset _))).getD ∅,
    outerAvailability := s.outerAvailability, currentFact := nextFact s i,
    currentDependencies := {dep i}, usedBindings := insert (nextBinding s) s.usedBindings,
    usedPackages := if s.parameter.isSome then insert (nextPackage s i) s.usedPackages else s.usedPackages,
    usedFacts := insert (nextFact s i) s.usedFacts }

def unchanged (s : ConcreteHeaderState) : ConcreteHeaderState :=
  { s with
    binding := nextBinding s,
    carriers := (s.parameter.map (fun p => ({(nextBinding s,p.identity)} : Finset _))).getD ∅,
    usedBindings := insert (nextBinding s) s.usedBindings }

def entry (affine : Bool) : ConcreteHeaderState :=
  let p := if affine then some ({identity := ⟨0⟩,type := ⟨0⟩,dependencies := {dep 0}} : Package) else none
  { binding := ⟨0⟩,parameter := p,
    carriers := (p.map (fun p => ({(⟨0⟩,p.identity)} : Finset _))).getD ∅,
    outerAvailability := .available,currentFact := ⟨0⟩,currentDependencies := {dep 0},
    usedBindings := {⟨0⟩},usedPackages := {⟨0⟩},usedFacts := {⟨0⟩} }

private theorem dep_scope (i : Fin 2) (b : BindingId) : Dependency.iteration b ≠ dep i := by
  simp [dep]
private theorem dep_live (affine : Bool) (s : ConcreteHeaderState) (i : Fin 2) : FactLive (sig affine) s (dep i) := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl|rfl <;> simp [FactLive,dep,sig]

theorem entry_wellFormed (affine : Bool) : HeaderWellFormed (sig affine) (entry affine) := by
  cases affine <;> constructor <;> simp [entry,sig,expectedCarriers,survivingDependencies,
    carriedDependencies,ScopeClosed,dep,FactLive]

theorem advance_dependencies (s : ConcreteHeaderState) (i : Fin 2) :
    survivingDependencies (advance s i) = {dep i} := by
  cases eq : s.parameter <;> simp [survivingDependencies,carriedDependencies,advance,advancedParameter,eq]

theorem advance_wellFormed {affine s} (wf : HeaderWellFormed (sig affine) s) (i : Fin 2) :
    HeaderWellFormed (sig affine) (advance s i) := by
  constructor
  · exact wf.externalSeparation
  · simpa [advance,advancedParameter,Option.map_map,Function.comp_def] using wf.types
  · rfl
  · simp [advance]
  · intro p present
    cases eq : s.parameter <;> simp [advance,advancedParameter,eq] at present
    case some old => cases present; simp [advance,eq]
  · simp [advance]
  · exact wf.availability
  · rw [advance_dependencies]; intro b; simpa using dep_scope i b
  · rw [advance_dependencies]; intro d member
    have eq := Finset.mem_singleton.mp member; subst d; exact dep_live affine _ i

theorem advance_frame (s : ConcreteHeaderState) (i : Fin 2) : ContinueFrame s (advance s i) := by
  refine ⟨next_binding_unused s,rfl,?_,Or.inr ⟨next_fact_unused s i,rfl⟩⟩
  cases eq : s.parameter with
  | none => exact .unchanged (by simp [advance,advancedParameter,eq]) (by simp [advance,eq])
  | some p =>
      exact .transformed p ⟨nextPackage s i,p.type,{dep i}⟩ eq
        (by simp [advance,advancedParameter,eq]) rfl (next_package_unused s i) (by simp [advance,eq])

theorem unchanged_wellFormed {affine s} (wf : HeaderWellFormed (sig affine) s) :
    HeaderWellFormed (sig affine) (unchanged s) := by
  exact ⟨wf.externalSeparation,wf.types,rfl,Finset.mem_insert_self _ _,wf.packageRecorded,wf.factRecorded,
    wf.availability,wf.scope,wf.dependencies⟩

theorem unchanged_frame (s : ConcreteHeaderState) : ContinueFrame s (unchanged s) :=
  ⟨next_binding_unused s,rfl,.unchanged rfl rfl,Or.inl ⟨rfl,rfl⟩⟩

def cyclic (affine : Bool) : Loop :=
  ⟨sig affine,entry affine,{.continue 0,.continue 1},fun i s outcome => match i,outcome with
    | .continue j,.continue t => t = advance s j
    | _,_ => False⟩

def finiteHeader (affine : Bool) : AbstractHeaderState :=
  ⟨sig affine,.unknown,.known {dep 0,dep 1},.unknown⟩

theorem entry_represented (affine : Bool) : Represents (entry affine) (finiteHeader affine) := by
  refine ⟨entry_wellFormed affine,by intros; trivial,?_,trivial⟩
  cases affine <;> simp [survivingDependencies,carriedDependencies,entry,finiteHeader,May.Contains]

theorem advanced_represented {affine s} (wf : HeaderWellFormed (sig affine) s) (i : Fin 2) :
    Represents (advance s i) (finiteHeader affine) := by
  refine ⟨advance_wellFormed wf i,by intros; trivial,?_,trivial⟩
  rw [advance_dependencies]
  intro d member; have eq := Finset.mem_singleton.mp member; subst d
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl|rfl <;> simp [finiteHeader,May.Contains]

theorem cyclic_continue {affine s} (wf : HeaderWellFormed (sig affine) s) (i : Fin 2) :
    Continue (cyclic affine) (.continue i) s (advance s i) := by
  have cases : i = 0 ∨ i = 1 := by omega
  refine ⟨?_,trivial,rfl,wf,advance_wellFormed wf i,advance_frame s i⟩
  rcases cases with rfl|rfl <;> simp [cyclic]

theorem cyclic_postFixpoint (affine : Bool) : PostFixpoint (cyclic affine) (finiteHeader affine) := by
  refine ⟨rfl,entry_represented affine,?_⟩
  intro s rep i t step
  have cls := step.classification
  cases i <;> simp [Edge.isContinue] at cls
  case «continue» j =>
    have eq : t = advance s j := step.body
    subst t; exact advanced_represented rep.1 j

end
end NewLang.F2.Counterexample
