import NewLang.Adjunct.KnownCallProofs
import NewLang.F1.Conditional.Model

namespace NewLang.Adjunct.LiveTail
open F0 F1.Backing F1.Occupancy
noncomputable section

structure WorldId where
  index : Nat
  deriving DecidableEq, Repr

/-- A fixed committed head field; its lifetime follows the head root. -/
structure LinkLayout where
  place : PlaceId
  incarnation : IncarnationId
  deriving DecidableEq, Repr

structure Link where
  payload : Option (WorldId × PtrToken)
  currentFact : ValueFactId
  occurrence : Option F1.Conditional.OccurrenceId
  payloadFact : Option ValueFactId
  deriving DecidableEq, Repr

inductive Dependency where
  | memory : F1.Conditional.Fact → Dependency
  | scope : F2.BindingId → Dependency
  deriving DecidableEq, Repr

inductive Stage where | donor | formals | localBundle | returned | unpacked | consumed
  deriving DecidableEq, Repr

inductive Field where | ptr | allocation | domain
  deriving DecidableEq, Repr

def Field.copyable : Field → Bool | .ptr => true | .allocation | .domain => false
def Field.discardable : Field → Bool | .ptr => true | .allocation | .domain => false

/-- A value envelope. The owner fields are views of the same unique memory
carrier entries, NOT a second owner ledger. No heap placement or Storage field. -/
structure Bundle where
  world : WorldId
  placement : F2.BindingId
  ptr : PtrToken
  region : BackingRegionId
  domain : DomainId
  allocationField : F2.BindingId
  domainField : F2.BindingId
  dependencies : Finset Dependency
  deriving DecidableEq

def Bundle.copyable (_ : Bundle) : Bool := [Field.ptr,.allocation,.domain].all Field.copyable
def Bundle.discardable (_ : Bundle) : Bool := [Field.ptr,.allocation,.domain].all Field.discardable

structure State where
  world : WorldId
  roots : KnownCall.Context
  memory : KnownCall.State
  layout : LinkLayout
  link : Link
  stage : Stage
  bundle : Option Bundle
  headScope : F2.BindingId
  scopes : Finset F2.BindingId
  writableRegions : Finset BackingRegionId
  ptrDependencies : Finset Dependency
  allocationDependencies : Finset Dependency
  domainDependencies : Finset Dependency
  /-- Additional precise head/external semantic survivors. -/
  externalDependencies : Finset Dependency
  usedFacts : Finset ValueFactId
  usedOccurrences : Finset F1.Conditional.OccurrenceId

def ownerDependencies (s : State) : Finset Dependency :=
  s.ptrDependencies ∪ s.allocationDependencies ∪ s.domainDependencies

def survivingDependencies (s : State) : Finset Dependency :=
  s.externalDependencies ∪ s.ptrDependencies ∪
    (if s.memory.tail.phase = .released then ∅ else s.allocationDependencies ∪ s.domainDependencies)

/-- Extra field/occurrence precision enriches the existing root facts. In
particular, stale occurrence facts never become new facts after a boundary. -/
def FactLive (s : State) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) => KnownCall.FactLive s.roots s.memory (.valueFact p vf) ∨
      (s.memory.head.phase = .typed ∧ p = s.layout.place ∧ vf = s.link.currentFact)
  | .fixed (.domainLive d) => KnownCall.FactLive s.roots s.memory (.domainLive d)
  | .occurrence o => s.memory.head.phase = .typed ∧ s.link.occurrence = some o
  | .payloadValue o vf => s.memory.head.phase = .typed ∧
      s.link.occurrence = some o ∧ s.link.payloadFact = some vf

def DependencyLive (s : State) : Dependency → Prop
  | .memory f => FactLive s f
  | .scope b => b ∈ s.scopes

def DependenciesValid (s : State) : Prop :=
  ∀ d ∈ survivingDependencies s, DependencyLive s d

def LayoutValid (s : State) : Prop :=
  s.layout.place ≠ s.roots.head.place ∧ s.layout.place ≠ s.roots.tail.place ∧
  s.layout.incarnation ≠ s.roots.head.incarnation ∧ s.layout.incarnation ≠ s.roots.tail.incarnation

def CarriesLiveH (s : State) (b : Bundle) : Prop :=
  b.world = s.world ∧ b.ptr = ⟨s.roots.tail.location,s.roots.tail.incarnation⟩ ∧
  b.region = s.roots.tail.extent.region ∧ b.domain = s.roots.tail.domain ∧
  s.memory.tail.phase = .typed ∧ s.memory.tail.domainLive = true ∧
  s.memory.carrier .tailAllocation = some b.allocationField ∧
  s.memory.carrier .tailDomain = some b.domainField ∧ b.dependencies = ownerDependencies s

def PackageShape (s : State) : Prop := match s.stage with
  | .localBundle | .returned => ∃ b, s.bundle = some b ∧ CarriesLiveH s b ∧
      b.placement ∈ s.memory.usedBindings ∧ ∀ r, s.memory.carrier r ≠ some b.placement
  | _ => s.bundle = none

structure WellFormed (s : State) : Prop where
  memory : KnownCall.WellFormed s.roots s.memory
  layout : LayoutValid s
  shape : s.link.payload.isSome = s.link.occurrence.isSome ∧
    s.link.payload.isSome = s.link.payloadFact.isSome
  parentRecorded : s.roots.head.currentFact ∈ s.usedFacts
  tailRecorded : s.roots.tail.currentFact ∈ s.usedFacts
  linkRecorded : s.link.currentFact ∈ s.usedFacts
  payloadRecorded : ∀ vf, s.link.payloadFact = some vf → vf ∈ s.usedFacts
  occurrenceRecorded : ∀ o, s.link.occurrence = some o → o ∈ s.usedOccurrences
  dependencies : DependenciesValid s
  package : PackageShape s
  /-- Live lexical bindings participate in historical binding freshness. -/
  scopeRecorded : ∀ b ∈ s.scopes, b ∈ s.memory.usedBindings

structure HeadRef where
  world : WorldId
  root : PtrToken
  field : LinkLayout
  domain : DomainId
  scope : F2.BindingId
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

/-- Numeric identities alone are insufficient across different execution worlds. -/
structure Arguments where
  world : WorldId
  tail : KnownCall.Arguments

/-- Head and tail parameters are independent symbolic records. These equalities
are obligations, not a signature-derived grant. -/
structure HeadRequirement (s : State) (r : HeadRef) (args : Arguments) : Prop where
  world : r.world = s.world
  root : r.root = ⟨s.roots.head.location,s.roots.head.incarnation⟩
  field : r.field = s.layout
  governing : r.domain = s.roots.head.domain
  scopeIdentity : r.scope = s.headScope
  liveScope : r.scope ∈ s.scopes
  read : r.read = true
  write : r.write = true
  readAccess : s.roots.head.extent.region ∈ s.memory.readableRegions
  writeAccess : s.roots.head.extent.region ∈ s.writableRegions
  someExactTail : s.link.payload = some (args.world,args.tail.ptr.token)

/-- All dependencies of retained values, including old Copy link and the
returned owner fields, must remain live after head Change/Reset. -/
def EndsAtDetach (s : State) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) =>
      (p = s.roots.head.place ∧ vf = s.roots.head.currentFact) ∨
      (p = s.layout.place ∧ vf = s.link.currentFact)
  | .fixed (.domainLive _) => False
  | .occurrence o => s.link.occurrence = some o
  | .payloadValue o vf => s.link.occurrence = some o ∧ s.link.payloadFact = some vf

def DetachGuard (s : State) : Prop :=
  (∀ f, f ∈ s.roots.head.dependencies ∨ f ∈ s.roots.tail.dependencies ∨
    f ∈ s.memory.externalDependencies → f ≠ .valueFact s.roots.head.place s.roots.head.currentFact) ∧
  (∀ d ∈ survivingDependencies s, ∀ f, d = .memory f → ¬ EndsAtDetach s f)

def ResultNonescape (s : State) : Prop :=
  ∀ b ∈ s.scopes, Dependency.scope b ∉ ownerDependencies s

structure Plan where
  formalA : F2.BindingId
  formalD : F2.BindingId
  localPlacement : F2.BindingId
  localA : F2.BindingId
  localD : F2.BindingId
  returnPlacement : F2.BindingId
  returnA : F2.BindingId
  returnD : F2.BindingId
  parentFact : ValueFactId
  linkFact : ValueFactId

def Plan.bindings (p : Plan) : List F2.BindingId :=
  [p.formalA,p.formalD,p.localPlacement,p.localA,p.localD,p.returnPlacement,p.returnA,p.returnD]

/-- Historical freshness is required across all publication boundaries. -/
structure FreshPlan (s : State) (p : Plan) : Prop where
  distinct : p.bindings.Nodup
  unused : ∀ b ∈ p.bindings, b ∉ s.memory.usedBindings
  valueScopes : ∀ b ∈ p.bindings, KnownCall.Blocker.allocationValue b ∉ s.memory.blockers ∧
    KnownCall.Blocker.domainValue b ∉ s.memory.blockers
  parentFresh : p.parentFact ∉ s.usedFacts
  linkFresh : p.linkFact ∉ s.usedFacts
  differentFacts : p.parentFact ≠ p.linkFact

inductive Command where | detach | construct (fields : List Field) | returnValue | finishTail
  deriving DecidableEq, Repr

def selectedBody : List Command := [.detach,.construct [.ptr,.allocation,.domain],.returnValue]
/-- Tiny semantic body skeleton, NOT source grammar/AST/typechecker. No caller
or constructor certificate is produced by satisfying this static check. -/
def DefinitionChecked (body : List Command) : Prop := body = selectedBody

def formalEntry (s : State) (p : Plan) : State :=
  {s with memory := KnownCall.transfer s.memory p.formalA p.formalD, stage := .formals}

def detach (s : State) (p : Plan) : State :=
  {s with
    roots := {s.roots with head := {s.roots.head with currentFact := p.parentFact}}
    link := ⟨none,p.linkFact,none,none⟩
    usedFacts := insert p.parentFact (insert p.linkFact s.usedFacts)}

def makeBundle (s : State) (placement a d : F2.BindingId) : Bundle :=
  ⟨s.world,placement,⟨s.roots.tail.location,s.roots.tail.incarnation⟩,
    s.roots.tail.extent.region,s.roots.tail.domain,a,d,ownerDependencies s⟩

def package (s : State) (placement a d : F2.BindingId) (stage : Stage) : State :=
  {s with
    memory := {KnownCall.transfer s.memory a d with
      usedBindings := insert placement (KnownCall.transfer s.memory a d).usedBindings}
    stage := stage
    bundle := some (makeBundle s placement a d)}

def producerPost (s : State) (p : Plan) : State :=
  package (package (detach (formalEntry s p) p) p.localPlacement p.localA p.localD .localBundle)
    p.returnPlacement p.returnA p.returnD .returned

/-- Actual caller must prove all relative obligations independently. -/
structure ActualCallApplicable (g : Geometry) (s : State) (r : HeadRef) (args : Arguments) (p : Plan) : Prop where
  context : KnownCall.ContextValid g s.roots
  pre : WellFormed s
  donor : s.stage = .donor
  world : args.world = s.world
  tail : KnownCall.RequiredAtEntry s.roots s.memory args.tail
  head : HeadRequirement s r args
  fresh : FreshPlan s p
  detach : DetachGuard s
  nonescape : ResultNonescape s

def ProducerCall (g : Geometry) (body : List Command) (s : State) (r : HeadRef)
    (args : Arguments) (p : Plan) (post : State) : Prop :=
  DefinitionChecked body ∧ ActualCallApplicable g s r args p ∧ post = producerPost s p

/-- Placement availability is separate from the unique underlying A/D entries. -/
def DirectTailAvailable (s : State) (a d : F2.BindingId) : Prop :=
  (s.stage = .donor ∨ s.stage = .formals ∨ s.stage = .unpacked) ∧
    s.memory.carrier .tailAllocation = some a ∧ s.memory.carrier .tailDomain = some d

def closeHeadScope (s : State) : State := {s with scopes := s.scopes.erase s.headScope}
def ScopeExitGuard (s : State) : Prop := Dependency.scope s.headScope ∉ survivingDependencies s

def KnownReturn (s : State) : Prop :=
  ∃ g body pre r args p, ProducerCall g body pre r args p s

def KnownReturnAfterScope (s : State) : Prop :=
  ∃ before, KnownReturn before ∧ ScopeExitGuard before ∧ s = closeHeadScope before

structure UnpackInput (s : State) (b : Bundle) (a d : F2.BindingId) : Prop where
  origin : KnownReturnAfterScope s
  returned : s.stage = .returned
  present : s.bundle = some b
  scopeEnded : s.headScope ∉ s.scopes
  fresh : KnownCall.FreshParameters s.memory a d

def unpack (s : State) (a d : F2.BindingId) : State :=
  {s with memory := KnownCall.transfer s.memory a d, stage := .unpacked, bundle := none}

/-- Raw candidate for publication rollback specification, not an executable checker. -/
def checkedProducer (g : Geometry) (body : List Command) (s : State) (r : HeadRef)
    (args : Arguments) (p : Plan) : State × Option Bundle :=
  by
    classical
    exact if DefinitionChecked body ∧ ActualCallApplicable g s r args p then
      (producerPost s p,(producerPost s p).bundle) else (s,none)

/-- Independently discharged after whole destructure, not inferred from nominal type. -/
def terminalPost (s : State) (a d : F2.BindingId) : State :=
  {s with memory := KnownCall.callPost s.memory a d, stage := .consumed, bundle := none}

def TerminalGuard (s : State) : Prop :=
  ∀ d ∈ s.externalDependencies ∪ s.ptrDependencies, ∀ f, d = .memory f →
    f ≠ .fixed (.valueFact s.roots.tail.place s.roots.tail.currentFact) ∧
    f ≠ .fixed (.domainLive s.roots.tail.domain)

def TerminalCall (g : Geometry) (s : State) (args : Arguments) (a d : F2.BindingId) : Prop :=
  WellFormed s ∧ s.stage = .unpacked ∧ s.headScope ∉ s.scopes ∧
    args.world = s.world ∧ KnownCall.Call g s.roots s.memory args.tail a d (KnownCall.callPost s.memory a d) ∧ TerminalGuard s

end
end NewLang.Adjunct.LiveTail
