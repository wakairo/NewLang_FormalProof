import NewLang.Adjunct.LiveTailProofs

namespace NewLang.Adjunct.Custody
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- The local sum has implicit lexical lifetime identity, not a third heap Domain value. -/
structure LocalLifetimeId where
  index : Nat
  deriving DecidableEq, Repr
structure LocalRoot where
  location : RootLocationId
  place : PlaceId
  incarnation : IncarnationId
  governing : LocalLifetimeId
  binding : F2.BindingId
  callerOwned : Bool
  writable : Bool
  deriving DecidableEq, Repr

inductive Tag where | none | some
  deriving DecidableEq, Repr
/-- Source/control evidence and concrete current tag are deliberately separate. -/
inductive Knowledge where
  | initializedNone : ValueFactId → Knowledge
  | replacedNone : ValueFactId → Knowledge
  | unknown | maySome
  deriving DecidableEq, Repr
inductive Holder where | packet | formal | custody | displaced | saved | unpacked
  deriving DecidableEq, Repr
inductive Choice where | pending | adopted | refused
  deriving DecidableEq, Repr
inductive Route where
  | beforeAdopt | afterAdopt | preRefusalRelease | refusalUnpacked | refusalReleased
  | extracted | recovered | savedUnpacked | savedReleased | complete
  deriving DecidableEq, Repr
inductive Origin where | adoption | extraction | other
  deriving DecidableEq, Repr
structure OldSum where
  tag : Tag
  origin : Origin
  knowledge : Knowledge
  sourceFact : ValueFactId
  deriving DecidableEq, Repr
structure Sink where
  world : LiveTail.WorldId
  root : LocalRoot
  scope : F2.BindingId
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

/-- One original tail owner only. Holder support may be malformed (duplicated or
lost), so uniqueness/coverage are invariants to preserve, not datatype shortcuts.
The packet metadata and holder support view the EXISTING unique A/D carrier table. -/
structure State where
  heap : LiveTail.State
  approved : LiveTail.State
  container : LocalRoot
  available : Bool
  tag : Tag
  currentFact : ValueFactId
  occurrence : Option F1.Conditional.OccurrenceId
  payloadFact : Option ValueFactId
  packet : LiveTail.Bundle
  holders : Finset Holder
  oldSum : Option OldSum
  knowledge : Knowledge
  choice : Choice
  route : Route
  loans : Finset F2.BindingId
  aliases : List Sink
  extraDependencies : Finset LiveTail.Dependency
  usedFacts : Finset ValueFactId
  usedOccurrences : Finset F1.Conditional.OccurrenceId

/-- Static capability: every variant is nonCopy/nonDiscardable. -/
def optionCopyable (_ : Tag) : Bool := [LiveTail.Field.ptr,.allocation,.domain].all LiveTail.Field.copyable
def optionDiscardable (_ : Tag) : Bool := [LiveTail.Field.ptr,.allocation,.domain].all LiveTail.Field.discardable

def SourceNone (k : Knowledge) (fact : ValueFactId) : Prop :=
  k = .initializedNone fact ∨ k = .replacedNone fact

def KnowledgeSound (s : State) : Prop :=
  match s.knowledge with
  | .initializedNone f | .replacedNone f => s.available = true ∧ s.tag = .none ∧ s.currentFact = f
  | .unknown | .maySome => True

def LocalFactLive (s : State) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) => s.available = true ∧ p = s.container.place ∧ vf = s.currentFact
  | .fixed (.domainLive _) => False
  | .occurrence o => s.available = true ∧ s.occurrence = some o
  | .payloadValue o vf => s.available = true ∧ s.occurrence = some o ∧ s.payloadFact = some vf

def FactLive (s : State) (f : F1.Conditional.Fact) : Prop :=
  LiveTail.FactLive s.heap f ∨ LocalFactLive s f

def DependencyLive (s : State) : LiveTail.Dependency → Prop
  | .memory f => FactLive s f
  | .scope b => b ∈ s.heap.scopes ∪ s.loans

def DependenciesValid (s : State) : Prop :=
  ∀ d ∈ s.extraDependencies, DependencyLive s d

def EndsAtChange (s : State) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) => p = s.container.place ∧ vf = s.currentFact
  | .fixed (.domainLive _) => False
  | .occurrence o => s.occurrence = some o
  | .payloadValue o vf => s.occurrence = some o ∧ s.payloadFact = some vf

def ChangeGuard (s : State) : Prop :=
  ∀ d ∈ s.extraDependencies, ∀ f, d = .memory f → ¬ EndsAtChange s f

def ScopeGuard (s : State) (b : F2.BindingId) : Prop :=
  LiveTail.Dependency.scope b ∉ s.extraDependencies ∧
  LiveTail.Dependency.scope b ∉ LiveTail.ownerDependencies s.heap

def OriginalData (s : State) : Prop :=
  ∃ b, s.approved.bundle = some b ∧ s.packet.world = b.world ∧ s.packet.ptr = b.ptr ∧
    s.packet.region = b.region ∧ s.packet.domain = b.domain ∧ s.packet.dependencies = b.dependencies

def LocalDistinct (s : State) : Prop :=
  s.container.location ≠ s.heap.roots.head.location ∧ s.container.location ≠ s.heap.roots.tail.location ∧
  s.container.place ≠ s.heap.roots.head.place ∧ s.container.place ≠ s.heap.roots.tail.place ∧
  s.container.place ≠ s.heap.layout.place ∧
  s.container.incarnation ≠ s.heap.roots.head.incarnation ∧ s.container.incarnation ≠ s.heap.roots.tail.incarnation

structure OwnerFrame (g : Geometry) (s : State) : Prop where
  heap : LiveTail.WellFormed s.heap
  envelope : s.heap.stage = .consumed ∧ s.heap.bundle = none
  context : KnownCall.ContextValid g s.heap.roots
  approved : LiveTail.KnownReturnAfterScope s.approved
  roots : s.heap.roots = s.approved.roots
  world : s.heap.world = s.approved.world
  original : OriginalData s
  localDistinct : LocalDistinct s
  localRecorded : s.container.binding ∈ s.heap.memory.usedBindings
  cover : s.heap.memory.tail.phase = .typed → ∃ h, s.holders = {h}
  released : s.heap.memory.tail.phase = .released → s.holders = ∅
  correlation : s.heap.memory.tail.phase = .typed → LiveTail.CarriesLiveH s.heap s.packet
  placementRecorded : s.heap.memory.tail.phase = .typed → s.packet.placement ∈ s.heap.memory.usedBindings
  placementSeparate : s.heap.memory.tail.phase = .typed →
    ∀ r, s.heap.memory.carrier r ≠ some s.packet.placement

structure WellFormed (g : Geometry) (s : State) : Prop extends OwnerFrame g s where
  currentRecorded : s.currentFact ∈ s.usedFacts
  occurrenceRecorded : ∀ o, s.occurrence = some o → o ∈ s.usedOccurrences
  payloadRecorded : ∀ vf, s.payloadFact = some vf → vf ∈ s.usedFacts
  knowledge : KnowledgeSound s
  shape : (s.tag = .some ↔ s.occurrence.isSome = true) ∧
    (s.tag = .some ↔ s.payloadFact.isSome = true)
  custody : (Holder.custody ∈ s.holders ↔ s.available = true ∧ s.tag = .some)
  displaced : (Holder.displaced ∈ s.holders ↔ ∃ o, s.oldSum = some o ∧ o.tag = .some)
  dependencies : DependenciesValid s
  refusal : s.choice = .refused → s.tag = .none

structure Supply where
  placement : F2.BindingId
  allocation : F2.BindingId
  domain : F2.BindingId

def Supply.fresh (s : State) (p : Supply) : Prop :=
  p.placement ∉ s.heap.memory.usedBindings ∧
  KnownCall.FreshParameters s.heap.memory p.allocation p.domain ∧
  p.placement ≠ p.allocation ∧ p.placement ≠ p.domain

/-- Rebind one complete original packet. No root/region/domain or dependency rewriting. -/
def rehome (s : State) (donor target : Holder) (p : Supply) : State :=
  {s with
    heap := {(s.heap) with stage := .consumed,bundle := none,memory := {KnownCall.transfer s.heap.memory p.allocation p.domain with
      usedBindings := insert p.placement (KnownCall.transfer s.heap.memory p.allocation p.domain).usedBindings}}
    packet := {s.packet with placement := p.placement,allocationField := p.allocation,domainField := p.domain}
    holders := insert target (s.holders.erase donor)}

/-- The ref's referent is caller C. All aliases query this SAME state; no noalias premise. -/
def SinkValid (s : State) (r : Sink) : Prop :=
  r.world = s.heap.world ∧ r.root = s.container ∧ s.container.callerOwned = true ∧
  s.available = true ∧ r.scope ∈ s.loans ∧ r.read = true ∧ r.write = true ∧ s.container.writable = true

def currentThrough (s : State) (r : Sink) : Option Tag :=
  if r.world = s.heap.world ∧ r.root = s.container then some s.tag else none

def invalidateKnowledge (s : State) : State := {s with knowledge := .unknown}

def packetArguments (s : State) : KnownCall.Arguments :=
  ⟨⟨s.packet.ptr,⟨s.packet.region,⟨true,true⟩⟩⟩,s.packet.region,
    s.packet.allocationField,s.packet.domain,s.packet.domainField⟩

/-- Moving the owner keeps the heap lifetime live. It requires no EndRoot,
Discardable, platform or root/domain/region-ending authority. Exact current
identity and owner fields come independently from pre-WellFormed correlation. -/
structure ReadyPacket (s : State) : Prop where
  live : s.heap.memory.tail.phase = .typed
  allocationScope : KnownCall.Blocker.allocationValue s.packet.allocationField ∉ s.heap.memory.blockers
  domainScope : KnownCall.Blocker.domainValue s.packet.domainField ∉ s.heap.memory.blockers

structure AdoptPlan where
  formal : Supply
  payload : Supply
  frame : F2.BindingId
  currentFact : ValueFactId
  payloadFact : ValueFactId
  occurrence : F1.Conditional.OccurrenceId

def AdoptPlan.bindings (p : AdoptPlan) : List F2.BindingId :=
  [p.frame,p.formal.placement,p.formal.allocation,p.formal.domain,
    p.payload.placement,p.payload.allocation,p.payload.domain]

def AdoptFresh (s : State) (p : AdoptPlan) : Prop :=
  p.bindings.Nodup ∧ (∀ b ∈ p.bindings, b ∉ s.heap.memory.usedBindings) ∧
  (∀ b ∈ p.bindings, KnownCall.Blocker.allocationValue b ∉ s.heap.memory.blockers ∧
    KnownCall.Blocker.domainValue b ∉ s.heap.memory.blockers) ∧
  p.currentFact ∉ s.usedFacts ∧ p.payloadFact ∉ s.usedFacts ∧
  p.currentFact ≠ p.payloadFact ∧ p.occurrence ∉ s.usedOccurrences

inductive Command where
  | replaceSome | consumeDisplacedNone | returnUnit
  | storeSome | dropOld | someWildcard | returnFailure
  deriving DecidableEq, Repr

def selectedBody : List Command := [.replaceSome,.consumeDisplacedNone,.returnUnit]
def DefinitionChecked (body : List Command) : Prop := body = selectedBody

structure Applicable (g : Geometry) (s : State) (r : Sink) (p : AdoptPlan) : Prop where
  pre : WellFormed g s
  packet : Holder.packet ∈ s.holders
  oldAbsent : s.oldSum = none
  pending : s.choice = .pending
  site : s.route = .beforeAdopt
  exactNone : SourceNone s.knowledge s.currentFact
  sink : SinkValid s r
  ready : ReadyPacket s
  fresh : AdoptFresh s p
  heapFresh : p.occurrence ∉ s.heap.usedOccurrences ∧
    p.currentFact ∉ s.heap.usedFacts ∧ p.payloadFact ∉ s.heap.usedFacts
  change : ChangeGuard s
  sinkScope : ScopeGuard s r.scope
  frameScope : ScopeGuard s p.frame
  headEnded : s.heap.headScope ∉ s.heap.scopes
  headEscape : ScopeGuard s s.heap.headScope

/-- Caller-visible atomic whole sum update; old None is an explicit value result. -/
def adoptCandidate (s : State) (p : AdoptPlan) : State :=
  let moved := rehome s .packet .custody p.payload
  {moved with
    heap := {(moved.heap) with memory := {(moved.heap.memory) with
      usedBindings := moved.heap.memory.usedBindings ∪ p.bindings.toFinset}}
    tag := .some
    currentFact := p.currentFact
    occurrence := some p.occurrence
    payloadFact := some p.payloadFact
    oldSum := some ⟨s.tag,.adoption,s.knowledge,s.currentFact⟩
    knowledge := .unknown
    choice := .adopted
    route := .afterAdopt
    usedFacts := insert p.currentFact (insert p.payloadFact s.usedFacts)
    usedOccurrences := insert p.occurrence s.usedOccurrences}

inductive MatchSite where | recipientDisplaced | callerFinal | elsewhere
  deriving DecidableEq, Repr

def NoneOnlyLegal (site : MatchSite) (s : State) : Prop := match site with
  | .recipientDisplaced => ∃ old, s.oldSum = some old ∧ old.origin = .adoption ∧
      old.tag = .none ∧ SourceNone old.knowledge old.sourceFact
  | .callerFinal => s.available = true ∧ s.tag = .none ∧
      s.knowledge = .replacedNone s.currentFact ∧ s.loans = ∅ ∧ s.oldSum = none ∧
      (s.route = .savedReleased ∨ (s.route = .recovered ∧ s.choice = .refused))
  | .elsewhere => False

def consumeDisplacedNone (s : State) : State := {s with oldSum := none}
def recipientPost (s : State) (p : AdoptPlan) : State := consumeDisplacedNone (adoptCandidate s p)

def RecipientCall (g : Geometry) (body : List Command) (s : State) (r : Sink)
    (p : AdoptPlan) (post : State) : Prop :=
  DefinitionChecked body ∧ Applicable g s r p ∧ post = recipientPost s p

def checkedRecipient (g : Geometry) (body : List Command) (s : State) (r : Sink) (p : AdoptPlan) : State := by
  classical
  exact if DefinitionChecked body ∧ Applicable g s r p then recipientPost s p else s

/-- Refusal is a PRE-consume application choice, not a runtime-failing recipient. -/
def refuse (s : State) : State := {s with choice := .refused,route := .preRefusalRelease}

def openLoan (s : State) (scope : F2.BindingId) : State :=
  {s with
    loans := insert scope s.loans,
    heap := {(s.heap) with memory := {(s.heap.memory) with usedBindings := insert scope s.heap.memory.usedBindings}}}
/-- Source-level fresh scope permission, separate from the raw state update. -/
structure LoanStep (g : Geometry) (s : State) (scope : F2.BindingId) (post : State) : Prop where
  pre : WellFormed g s
  fresh : scope ∉ s.heap.memory.usedBindings
  post : post = openLoan s scope

def closeLoan (s : State) (scope : F2.BindingId) : State :=
  {s with loans := s.loans.erase scope, aliases := s.aliases.filter (fun r => r.scope != scope)}

structure ExtractPlan where
  old : Supply
  currentFact : ValueFactId

structure ExtractApplicable (g : Geometry) (s : State) (r : Sink) (p : ExtractPlan) : Prop where
  pre : WellFormed g s
  sink : SinkValid s r
  oldAbsent : s.oldSum = none
  site : s.route = .afterAdopt ∨ s.route = .refusalReleased
  chosen : s.choice = .adopted ∨ s.choice = .refused
  refusalFinished : s.choice = .refused → s.heap.memory.tail.phase = .released
  fresh : p.old.fresh s
  factFresh : p.currentFact ∉ s.usedFacts
  heapFactFresh : p.currentFact ∉ s.heap.usedFacts
  ready : s.tag = .some → ReadyPacket s
  change : ChangeGuard s
  scope : ScopeGuard s r.scope

def extractPost (s : State) (p : ExtractPlan) : State :=
  let moved := if s.tag = .some then rehome s .custody .displaced p.old else s
  {moved with
    tag := .none,currentFact := p.currentFact,occurrence := none,payloadFact := none,
    knowledge := .replacedNone p.currentFact,route := .extracted,
    oldSum := some ⟨s.tag,.extraction,s.knowledge,s.currentFact⟩,
    usedFacts := insert p.currentFact s.usedFacts}

structure RecoverApplicable (g : Geometry) (s : State) (p : Supply) : Prop where
  pre : WellFormed g s
  old : ∃ old, s.oldSum = some old ∧ old.origin = .extraction
  scopesEnded : s.loans = ∅
  empty : s.tag = .none
  site : s.route = .extracted
  fresh : p.fresh s
  ready : (∃ old, s.oldSum = some old ∧ old.tag = .some) → ReadyPacket s

/-- Exhaustive None/Some by-value match; no wildcard Drop. Occurrence is absent
from value data: it is not transferred to the saved packet. -/
def recoverPost (s : State) (p : Supply) : State :=
  let moved := if Holder.displaced ∈ s.holders then rehome s .displaced .saved p else s
  {moved with oldSum := none,route := .recovered}

structure UnpackApplicable (g : Geometry) (s : State) (p : Supply) : Prop where
  pre : WellFormed g s
  present : Holder.saved ∈ s.holders ∨ Holder.packet ∈ s.holders
  site : (s.route = .recovered ∧ Holder.saved ∈ s.holders) ∨
    (s.route = .preRefusalRelease ∧ Holder.packet ∈ s.holders)
  loansEnded : s.loans = ∅
  empty : s.tag = .none
  oldAbsent : s.oldSum = none
  fresh : p.fresh s
  ready : ReadyPacket s

def unpackPost (s : State) (p : Supply) : State :=
  {(rehome s (if Holder.saved ∈ s.holders then .saved else .packet) .unpacked p) with
    route := if Holder.saved ∈ s.holders then .savedUnpacked else .refusalUnpacked}

def receiverView (s : State) : LiveTail.State := {(s.heap) with stage := .unpacked,bundle := none}
def ExtraTerminalGuard (s : State) : Prop :=
  ∀ d ∈ s.extraDependencies, ∀ f, d = .memory f →
    f ≠ .fixed (.valueFact s.heap.roots.tail.place s.heap.roots.tail.currentFact) ∧
    f ≠ .fixed (.domainLive s.heap.roots.tail.domain)

structure TerminalApplicable (g : Geometry) (s : State) (a d : F2.BindingId) : Prop where
  pre : WellFormed g s
  holder : Holder.unpacked ∈ s.holders
  site : s.route = .savedUnpacked ∨ s.route = .refusalUnpacked
  scopesEnded : s.loans = ∅
  empty : s.tag = .none
  oldAbsent : s.oldSum = none
  base : LiveTail.TerminalCall g (receiverView s)
    ⟨s.packet.world,packetArguments s⟩ a d
  extra : ExtraTerminalGuard s

def terminalPost (s : State) (a d : F2.BindingId) : State :=
  {s with
    heap := LiveTail.terminalPost (receiverView s) a d, holders := ∅,
    route := if s.route = .savedUnpacked then .savedReleased else .refusalReleased}

structure FinalApplicable (g : Geometry) (s : State) : Prop where
  pre : WellFormed g s
  exactNone : NoneOnlyLegal .callerFinal s
  change : ChangeGuard s

def consumeFinalNone (s : State) : State := {s with available := false,knowledge := .unknown,route := .complete}

end
end NewLang.Adjunct.Custody
