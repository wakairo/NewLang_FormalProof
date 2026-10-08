import NewLang.F1.Occupancy.Model
import NewLang.F2.Model

namespace NewLang.Adjunct.KnownCall
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Exactly the two existing roots; this module has no allocation/initialize rule. -/
inductive Site where | head | tail
  deriving DecidableEq, Repr
inductive Role where | headAllocation | headDomain | tailAllocation | tailDomain
  deriving DecidableEq, Repr
inductive Phase where | typed | emptySlot | raw | released
  deriving DecidableEq, Repr

structure Root where
  location : RootLocationId
  place : PlaceId
  incarnation : IncarnationId
  currentFact : ValueFactId
  package : PackageId
  domain : DomainId
  extent : Extent
  dependencies : Finset F0.Fact
  discardable : Bool

/-- Fixed identities of the already allocated roots, never parameter-owned root identities. -/
structure Context where
  head : Root
  tail : Root
  type : F1.Occupancy.TypeId
  size : Nat

def Context.root (c : Context) : Site → Root | .head => c.head | .tail => c.tail

structure ContextValid (g : Geometry) (c : Context) : Prop where
  regions : c.head.extent.region ≠ c.tail.extent.region
  locations : c.head.location ≠ c.tail.location
  places : c.head.place ≠ c.tail.place
  incarnations : c.head.incarnation ≠ c.tail.incarnation
  facts : c.head.currentFact ≠ c.tail.currentFact
  domains : c.head.domain ≠ c.tail.domain
  packages : c.head.package ≠ c.tail.package
  nonempty : 0 < c.size
  full : ∀ i, (c.root i).extent.range = ⟨0, g.capacity (c.root i).extent.region⟩
  exactSize : ∀ i, (c.root i).extent.range.length = c.size
  disjoint : Disjoint (c.head.extent.footprint g) (c.tail.extent.footprint g)

/-- Selected finite scope blockers, not permissions inferred from parameter types. -/
inductive Blocker where
  | allocationValue : F2.BindingId → Blocker
  | domainValue : F2.BindingId → Blocker
  | root : IncarnationId → Blocker
  | domain : DomainId → Blocker
  | region : BackingRegionId → Blocker
  deriving DecidableEq, Repr

structure Cell where
  phase : Phase
  domainLive : Bool
  /-- Proof-only release event count. -/
  releases : Nat
  deriving DecidableEq, Repr

structure State where
  head : Cell
  tail : Cell
  carrier : Role → Option F2.BindingId
  usedBindings : Finset F2.BindingId
  externalDependencies : Finset F0.Fact
  blockers : Finset Blocker
  /-- Source-founded provenance/access facts supplied by the caller, not argument types. -/
  issuedPtrs : Finset PtrToken
  readableRegions : Finset BackingRegionId
  /-- Explicit primitive/platform precondition, never supplied by a ptr. -/
  platformReady : Bool

def State.cell (s : State) : Site → Cell | .head => s.head | .tail => s.tail

def allocationRole : Site → Role | .head => .headAllocation | .tail => .tailAllocation
def domainRole : Site → Role | .head => .headDomain | .tail => .tailDomain

/-- Each original region has exactly one current occupancy responsibility until release.
A live root is state-owned, whereas slot/raw claims are value-owned. -/
def responsibility (c : Context) (s : State) (i : Site) : Option Claim :=
  match (s.cell i).phase with
  | .typed => some (.root c.type (c.root i).location (c.root i).extent)
  | .emptySlot => some (.slot c.type (c.root i).extent)
  | .raw => some (.storage (c.root i).extent)
  | .released => none

def FactLive (c : Context) (s : State) : F0.Fact → Prop
  | .valueFact p f => ∃ i, (s.cell i).phase = .typed ∧ (c.root i).place = p ∧ (c.root i).currentFact = f
  | .domainLive d => ∃ i, (s.cell i).domainLive = true ∧ (c.root i).domain = d

def DependenciesValid (c : Context) (s : State) : Prop :=
  (∀ i, (s.cell i).phase = .typed → ∀ f ∈ (c.root i).dependencies, FactLive c s f) ∧
  (∀ f ∈ s.externalDependencies, FactLive c s f)

structure WellFormed (c : Context) (s : State) : Prop where
  allocation : ∀ i, (∃ b, s.carrier (allocationRole i) = some b) ↔ (s.cell i).phase ≠ .released
  domain : ∀ i, (∃ b, s.carrier (domainRole i) = some b) ↔ (s.cell i).domainLive = true
  typedDomain : ∀ i, (s.cell i).phase = .typed → (s.cell i).domainLive = true
  slotDomain : ∀ i, (s.cell i).phase = .emptySlot → (s.cell i).domainLive = true
  releasedDomain : ∀ i, (s.cell i).phase = .released → (s.cell i).domainLive = false
  releaseCount : ∀ i, (s.cell i).releases = if (s.cell i).phase = .released then 1 else 0
  recorded : ∀ r b, s.carrier r = some b → b ∈ s.usedBindings
  unique : ∀ r q b, s.carrier r = some b → s.carrier q = some b → r = q
  dependencies : DependenciesValid c s

structure Arguments where
  ptr : AccessPtr
  allocationRegion : BackingRegionId
  allocationBinding : F2.BindingId
  domain : DomainId
  domainBinding : F2.BindingId

/-- Inferred finite entry REQUIREMENT. Its declaration does not prove it for any caller.
All three arguments have the same static types in matched and mismatched controls. -/
structure RequiredAtEntry (c : Context) (s : State) (a : Arguments) : Prop where
  headLive : s.head.phase = .typed
  live : s.tail.phase = .typed
  ptrRoot : a.ptr.token = ⟨c.tail.location, c.tail.incarnation⟩
  ptrRegion : a.ptr.evidence.region = c.tail.extent.region
  read : a.ptr.evidence.access.read = true
  issued : a.ptr.token ∈ s.issuedPtrs
  access : c.tail.extent.region ∈ s.readableRegions
  allocationRegion : a.allocationRegion = c.tail.extent.region
  allocation : s.carrier .tailAllocation = some a.allocationBinding
  domainIdentity : a.domain = c.tail.domain
  domain : s.carrier .tailDomain = some a.domainBinding
  allocationScope : .allocationValue a.allocationBinding ∉ s.blockers
  domainValueScope : .domainValue a.domainBinding ∉ s.blockers
  rootScope : .root c.tail.incarnation ∉ s.blockers
  domainScope : .domain c.tail.domain ∉ s.blockers
  regionScope : .region c.tail.extent.region ∉ s.blockers
  discardable : c.tail.discardable = true
  platform : s.platformReady = true

/-- No dependencies of the retained head/external packages may refer to either
ended tail current fact or finalized tail domain. The discarded tail is excluded. -/
def SurvivorGuard (c : Context) (s : State) : Prop :=
  ∀ f, (f ∈ c.head.dependencies ∨ f ∈ s.externalDependencies) →
    f ≠ .valueFact c.tail.place c.tail.currentFact ∧ f ≠ .domainLive c.tail.domain

structure FreshParameters (s : State) (a d : F2.BindingId) : Prop where
  allocationFresh : a ∉ s.usedBindings
  domainFresh : d ∉ s.usedBindings
  distinct : a ≠ d
  allocationScope : .allocationValue a ∉ s.blockers
  domainScope : .domainValue d ∉ s.blockers

def transfer (s : State) (a d : F2.BindingId) : State :=
  {s with
    carrier := fun r => match r with
      | .tailAllocation => some a | .tailDomain => some d | _ => s.carrier r,
    usedBindings := insert a (insert d s.usedBindings)}

/-- The heap root is not the freshly created parameter binding incarnation. -/
def endRoot (s : State) : State := {s with tail := {s.tail with phase := .emptySlot}}
def eraseSlot (s : State) : State := {s with tail := {s.tail with phase := .raw}}
def finalize (s : State) : State :=
  {s with
    tail := {s.tail with domainLive := false},
    carrier := fun r => if r = .tailDomain then none else s.carrier r}
def deallocate (s : State) : State :=
  {s with
    tail := {s.tail with phase := .released, releases := s.tail.releases + 1},
    carrier := fun r => if r = .tailAllocation then none else s.carrier r}

/-- Strict primitive order. Raw Storage exists only after EndRoot and erase_slot. -/
def receiver (s : State) : State := deallocate (finalize (eraseSlot (endRoot s)))
def callPost (s : State) (a d : F2.BindingId) : State := receiver (transfer s a d)

/-- No post-WellFormed oracle. Definition-time conditional evidence is proved in
Proofs; each actual caller must discharge this exact entry relation separately. -/
def Call (g : Geometry) (c : Context) (s : State) (args : Arguments)
    (a d : F2.BindingId) (post : State) : Prop :=
  ContextValid g c ∧ WellFormed c s ∧ RequiredAtEntry c s args ∧
    FreshParameters s a d ∧ SurvivorGuard c s ∧ post = callPost s a d

def CanDeallocate (c : Context) (s : State) (a : F2.BindingId) (raw : Extent) : Prop :=
  s.tail.phase = .raw ∧ s.tail.domainLive = false ∧
    s.carrier .tailAllocation = some a ∧ raw = c.tail.extent ∧ s.platformReady = true ∧
    .region c.tail.extent.region ∉ s.blockers ∧ s.tail.releases = 0

/-- Explicit attempted early/bypass release guard; a ptr is deliberately absent. -/
def CanEnd (c : Context) (s : State) (d : F2.BindingId) : Prop :=
  s.tail.phase = .typed ∧ s.carrier .tailDomain = some d ∧
    .root c.tail.incarnation ∉ s.blockers ∧ c.tail.discardable = true

def CanEraseSlot (s : State) : Prop := s.tail.phase = .emptySlot

def Governs (c : Context) (s : State) (o : IncarnationId) (d : DomainId) : Prop :=
  ∃ i, (s.cell i).phase = .typed ∧ (c.root i).incarnation = o ∧ (c.root i).domain = d

def CurrentLocator (c : Context) (s : State) (ptr : PtrToken) : Prop :=
  ∃ i, (s.cell i).phase = .typed ∧ ptr = ⟨(c.root i).location, (c.root i).incarnation⟩

def CanFinalize (c : Context) (s : State) (d : F2.BindingId) : Prop :=
  s.tail.phase = .raw ∧ s.tail.domainLive = true ∧ s.carrier .tailDomain = some d ∧
    .domain c.tail.domain ∉ s.blockers ∧
    (∀ o, ¬ Governs c s o c.tail.domain) ∧
    (∀ f, f ∈ c.head.dependencies ∨ f ∈ s.externalDependencies → f ≠ .domainLive c.tail.domain)

end
end NewLang.Adjunct.KnownCall
