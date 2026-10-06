import NewLang.F0.Package
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Basic

namespace NewLang.F2
open F0
noncomputable section

structure BindingId where
  index : Nat
  deriving DecidableEq, Repr
structure TypeId where
  index : Nat
  deriving DecidableEq, Repr
inductive Availability where | available | consumed
  deriving DecidableEq, Repr

/-- Existing blocking facts, or dependence on this loop's ending iteration.
Persistent ptr provenance is not automatically a blocking dependency. -/
inductive Dependency where
  | externalFact : F0.Fact → Dependency
  | iteration : BindingId → Dependency
  deriving DecidableEq, Repr

def ScopeClosed (deps : Finset Dependency) : Prop := ∀ b, Dependency.iteration b ∉ deps

structure Package where
  identity : PackageId
  type : TypeId
  dependencies : Finset Dependency
  deriving DecidableEq

/-- Bounded zero/one non-Copy slot, plus one captured affine availability and
one outer Copy/current-value component. No widened value is a concrete field. -/
structure ConcreteHeaderState where
  binding : BindingId
  parameter : Option Package
  carriers : Finset (BindingId × PackageId)
  outerAvailability : Availability
  currentFact : ValueFactId
  currentDependencies : Finset Dependency
  usedBindings : Finset BindingId
  usedPackages : Finset PackageId
  usedFacts : Finset ValueFactId

structure Signature where
  parameterType : Option TypeId
  entryAvailability : Availability
  outerPlace : PlaceId
  publicFacts : Finset F0.Fact

/-- Count and slot correspondence are derived from the single optional slot;
there is no separately stored arity that can disagree with its arguments. -/
def parameterCount (s : ConcreteHeaderState) : Nat := s.parameter.toList.length
def expectedCarriers (s : ConcreteHeaderState) : Finset (BindingId × PackageId) :=
  (s.parameter.map (fun p => ({(s.binding,p.identity)} : Finset _))).getD ∅
def carriedDependencies (s : ConcreteHeaderState) : Finset Dependency :=
  (s.parameter.map Package.dependencies).getD ∅
def survivingDependencies (s : ConcreteHeaderState) : Finset Dependency :=
  carriedDependencies s ∪ s.currentDependencies

def FactLive (sig : Signature) (s : ConcreteHeaderState) : Dependency → Prop
  | .externalFact f => f ∈ sig.publicFacts ∨ f = .valueFact sig.outerPlace s.currentFact
  | .iteration _ => False

structure HeaderWellFormed (sig : Signature) (s : ConcreteHeaderState) : Prop where
  externalSeparation : ∀ vf, .valueFact sig.outerPlace vf ∉ sig.publicFacts
  types : s.parameter.map Package.type = sig.parameterType
  affine : s.carriers = expectedCarriers s
  bindingRecorded : s.binding ∈ s.usedBindings
  packageRecorded : ∀ p, s.parameter = some p → p.identity ∈ s.usedPackages
  factRecorded : s.currentFact ∈ s.usedFacts
  availability : s.outerAvailability = sig.entryAvailability
  scope : ScopeClosed (survivingDependencies s)
  dependencies : ∀ d ∈ survivingDependencies s, FactLive sig s d

/-- Structural transfer evidence abstracts ordinary body operations. Transform
consumes the old responsibility and produces a fresh same-type package; its
new dependencies are checked in the exact candidate header, not erased. -/
inductive Carry (pre post : ConcreteHeaderState) : Prop where
  | unchanged : post.parameter = pre.parameter → post.usedPackages = pre.usedPackages → Carry pre post
  | transformed (old new : Package) : pre.parameter = some old → post.parameter = some new →
      new.type = old.type → new.identity ∉ pre.usedPackages →
      post.usedPackages = insert new.identity pre.usedPackages → Carry pre post

structure ContinueFrame (pre post : ConcreteHeaderState) : Prop where
  freshBinding : post.binding ∉ pre.usedBindings
  bindingHistory : post.usedBindings = insert post.binding pre.usedBindings
  carry : Carry pre post
  memory : (post.currentFact = pre.currentFact ∧ post.usedFacts = pre.usedFacts) ∨
    (post.currentFact ∉ pre.usedFacts ∧ post.usedFacts = insert post.currentFact pre.usedFacts)

structure ExitState where
  result : Package
  copy : Bool
  carriers : Finset PackageId
  outerAvailability : Availability
  currentFact : ValueFactId
  currentDependencies : Finset Dependency

def exitDependencies (s : ExitState) := s.result.dependencies ∪ s.currentDependencies
/-- Break/return do not inherit entry availability. Function-scope return
obligations beyond this one-loop iteration slice are body/caller obligations. -/
structure ExitWellFormed (s : ExitState) : Prop where
  affine : s.copy = false → s.carriers = {s.result.identity}
  scope : ScopeClosed (exitDependencies s)

inductive Edge where
  | continue : Fin 2 → Edge
  | break : Fin 2 → Edge
  | return : Fin 2 → Edge
  deriving DecidableEq, Repr
inductive Outcome where
  | continue : ConcreteHeaderState → Outcome
  | break : ExitState → Outcome
  | return : ExitState → Outcome

def Edge.isContinue : Edge → Prop
  | .continue _ => True | _ => False
def Edge.isBreak : Edge → Bool
  | .break _ => true | _ => false

/-- Supplied finite edge family stands for static reachability. Body is the
ordinary semantic transfer premise, including omitted expression evaluation;
no runtime fixture condition deletes an edge from this supplied family. -/
structure Loop where
  signature : Signature
  entry : ConcreteHeaderState
  edges : Finset Edge
  body : Edge → ConcreteHeaderState → Outcome → Prop

structure Continue (k : Loop) (edge : Edge) (pre post : ConcreteHeaderState) : Prop where
  supplied : edge ∈ k.edges
  classification : edge.isContinue
  body : k.body edge pre (.continue post)
  before : HeaderWellFormed k.signature pre
  after : HeaderWellFormed k.signature post
  frame : ContinueFrame pre post

def ExitFactsLive (sig : Signature) (s : ExitState) : Prop :=
  ∀ d ∈ exitDependencies s, ∃ f, d = .externalFact f ∧
    (f ∈ sig.publicFacts ∨ f = .valueFact sig.outerPlace s.currentFact)

structure Break (k : Loop) (edge : Edge) (pre : ConcreteHeaderState) (post : ExitState) : Prop where
  supplied : edge ∈ k.edges
  classification : edge.isBreak = true
  body : k.body edge pre (.break post)
  before : HeaderWellFormed k.signature pre
  after : ExitWellFormed post
  dependencies : ExitFactsLive k.signature post

structure Return (k : Loop) (edge : Edge) (pre : ConcreteHeaderState) (post : ExitState) : Prop where
  supplied : edge ∈ k.edges
  classification : ∃ i, edge = .return i
  body : k.body edge pre (.return post)
  before : HeaderWellFormed k.signature pre
  after : ExitWellFormed post
  dependencies : ExitFactsLive k.signature post

end
end NewLang.F2
