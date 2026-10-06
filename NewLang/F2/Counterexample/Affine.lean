import NewLang.F2.Counterexample.Cyclic

namespace NewLang.F2.Counterexample
open F0
noncomputable section

def duplicated : ConcreteHeaderState :=
  {advance (entry true) 0 with
    carriers := insert ((entry true).binding,⟨0⟩) (advance (entry true) 0).carriers}
def lost : ConcreteHeaderState := {advance (entry true) 0 with carriers := ∅}
def availabilityChanged : ConcreteHeaderState :=
  {advance (entry true) 0 with outerAvailability := .consumed}
def iterationEscaped : ConcreteHeaderState :=
  {advance (entry true) 0 with
    currentDependencies := insert (.iteration (entry true).binding) (advance (entry true) 0).currentDependencies}

theorem same_type_does_not_mean_same_package :
    (advance (entry true) 0).parameter.map Package.type = (entry true).parameter.map Package.type ∧
    (advance (entry true) 0).parameter.map Package.identity ≠ (entry true).parameter.map Package.identity :=
  transformed_affine_carry.2

theorem duplicated_affine_responsibility_rejected :
    duplicated.parameter.map Package.type = (sig true).parameterType ∧
    ScopeClosed (survivingDependencies duplicated) ∧
    ¬ HeaderWellFormed (sig true) duplicated := by
  refine ⟨rfl,(advance_wellFormed (entry_wellFormed true) 0).scope,?_⟩
  intro wf
  have single := wf.affine
  have old : ((entry true).binding,(⟨0⟩ : PackageId)) ∈ duplicated.carriers := by simp [duplicated]
  rw [single] at old
  simp [expectedCarriers,duplicated,advance,advancedParameter,entry,nextBinding,nextPackage] at old

theorem lost_affine_responsibility_rejected :
    lost.parameter.map Package.type = (sig true).parameterType ∧
    ScopeClosed (survivingDependencies lost) ∧ ¬ HeaderWellFormed (sig true) lost := by
  refine ⟨rfl,(advance_wellFormed (entry_wellFormed true) 0).scope,?_⟩
  intro wf
  have single := wf.affine
  simp [lost,expectedCarriers,advance,advancedParameter,entry] at single

theorem outer_availability_cannot_be_widened :
    availabilityChanged.carriers = expectedCarriers availabilityChanged ∧
    ¬ HeaderWellFormed (sig true) availabilityChanged := by
  refine ⟨rfl,?_⟩
  intro wf; have eq := wf.availability; cases eq

theorem iteration_local_dependency_cannot_escape :
    iterationEscaped.carriers = expectedCarriers iterationEscaped ∧
    ¬ HeaderWellFormed (sig true) iterationEscaped := by
  refine ⟨rfl,?_⟩
  intro wf
  exact wf.scope (entry true).binding (by simp [iterationEscaped,survivingDependencies])

/-- Distinct post-fork package identities remain alternatives at the same type. -/
theorem fork_identity_cannot_collapse_to_type :
    (advance (entry true) 0).parameter.map Package.type = (advance (entry true) 1).parameter.map Package.type ∧
    (advance (entry true) 0).parameter.map Package.identity ≠ (advance (entry true) 1).parameter.map Package.identity :=
  ⟨rfl,two_edges_distinct_alternatives.2.2.2.2⟩

def singletonOrigin : AbstractHeaderState :=
  {finiteHeader true with origins := .known {nextPackage (entry true) 0}}

theorem origin_singleton_loses_fork_alternative :
    Represents (advance (entry true) 0) singletonOrigin ∧
    ¬ Represents (advance (entry true) 1) singletonOrigin := by
  refine ⟨⟨(advanced_represented (entry_wellFormed true) 0).1,?_,
    (advanced_represented (entry_wellFormed true) 0).2.2⟩,?_⟩
  · intro p present
    simp [advance,advancedParameter,entry] at present; subst p
    simp [singletonOrigin,May.Contains,nextPackage,entry]
  · intro rep
    have member := rep.2.1 ⟨nextPackage (entry true) 1,⟨0⟩,{dep 1}⟩ rfl
    simp [singletonOrigin,May.Contains,nextPackage,entry] at member

def oldValueDependent : ConcreteHeaderState :=
  {entry true with
    parameter := some ⟨⟨0⟩,⟨0⟩,{.externalFact (.valueFact ⟨0⟩ ⟨0⟩)}⟩}
def mutatedUnchanged : ConcreteHeaderState :=
  {unchanged oldValueDependent with
    currentFact := nextFact oldValueDependent 0,
    usedFacts := insert (nextFact oldValueDependent 0) oldValueDependent.usedFacts}

theorem copy_mutation_does_not_clear_hidden_affine_blocker :
    HeaderWellFormed (sig true) oldValueDependent ∧
    mutatedUnchanged.parameter = oldValueDependent.parameter ∧
    ¬ HeaderWellFormed (sig true) mutatedUnchanged := by
  have wf : HeaderWellFormed (sig true) oldValueDependent := by
    constructor <;> simp [oldValueDependent,entry,sig,expectedCarriers,ScopeClosed,
      survivingDependencies,carriedDependencies,dep,FactLive]
  refine ⟨wf,rfl,?_⟩
  intro after
  have live := after.dependencies (.externalFact (.valueFact ⟨0⟩ ⟨0⟩))
    (by simp [mutatedUnchanged,unchanged,oldValueDependent,survivingDependencies,carriedDependencies])
  simp [FactLive,sig,mutatedUnchanged,nextFact,oldValueDependent,entry] at live

end
end NewLang.F2.Counterexample
