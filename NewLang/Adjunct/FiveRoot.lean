import NewLang.Adjunct.LiveTailProofs
import NewLang.F1.Reference
import NewLang.Declaration.Proofs

namespace NewLang.Adjunct.FiveRoot
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Closed source sites, not a generalized N-root allocator. -/
inductive Site where | src | a | b | c | dst
  deriving DecidableEq, Repr
inductive Field where | next | prev | child
  deriving DecidableEq, Repr

def Site.code : Site → Nat | .src => 0 | .a => 1 | .b => 2 | .c => 3 | .dst => 4
def Field.code : Field → Nat | .next => 0 | .prev => 1 | .child => 2
structure ProjectionId where
  index : Nat
  deriving DecidableEq, Repr

def projection (f : Field) : ProjectionId := ⟨f.code⟩
def parentPlace (i : Site) : PlaceId := ⟨i.code + 1⟩
def fieldPlace (i : Site) (f : Field) : PlaceId := ⟨100 + 10*i.code + f.code⟩
def fieldIncarnation (i : Site) (f : Field) : IncarnationId := ⟨100 + 10*i.code + f.code⟩

def layout (i : Site) : F1.StructuralLayout where
  places := {parentPlace i,fieldPlace i .next,fieldPlace i .prev,fieldPlace i .child}
  root := parentPlace i
  path := fun p => if p = parentPlace i then [] else if p = fieldPlace i .next then [0]
    else if p = fieldPlace i .prev then [1] else [2]

/-- World qualification is independent of branch-local numeric IDs. -/
structure Origin where
  world : LiveTail.WorldId
  ptr : PtrToken
  region : BackingRegionId
  domain : DomainId
  allocation : F2.BindingId
  domainBinding : F2.BindingId
  deriving DecidableEq, Repr

def original (w : LiveTail.WorldId) (i : Site) : Origin :=
  ⟨w,⟨⟨i.code+1⟩,⟨i.code+1⟩⟩,⟨i.code+1⟩,⟨i.code+1⟩,⟨2*i.code+1⟩,⟨2*i.code+2⟩⟩
def full (o : Origin) : Extent := ⟨o.region,⟨0,1⟩⟩
def reconstruct (w : LiveTail.WorldId) (i : Site) (o : Origin) : Prop := o = original w i
inductive Authority where | allocation : Origin → Authority | domain : Origin → Authority
  deriving DecidableEq, Repr

def expectedOwners (o : Origin) (c : KnownCall.Cell) : List Authority :=
  (if c.phase = .released then [] else [.allocation o]) ++
  (if c.domainLive then [.domain o] else [])
def expectedClaim (o : Origin) (c : KnownCall.Cell) : Option Claim := match c.phase with
  | .typed => some (.root ⟨0⟩ o.ptr.location (full o))
  | .emptySlot => some (.slot ⟨0⟩ (full o))
  | .raw => some (.storage (full o))
  | .released => none

def initialParent (i : Site) : ValueFactId := ⟨10*i.code+1⟩
def initialLink (i : Site) (f : Field) : LiveTail.Link :=
  ⟨none,⟨10*i.code+2+f.code⟩,none,none⟩
def initialFacts (i : Site) : Finset ValueFactId :=
  {initialParent i,(initialLink i .next).currentFact,(initialLink i .prev).currentFact,(initialLink i .child).currentFact}

/-- One completed opaque H type (claim type key 0) per Site. The three links
are fixed subobjects of that root, not independent lifetime/occupancy roots.
The source byte payload is an unchanged opaque Copy scalar in this slice. -/
structure State where
  world : LiveTail.WorldId
  successes : Nat
  origin : Site → Origin
  cell : Site → Option KnownCall.Cell
  owners : Site → List Authority
  claim : Site → Option Claim
  parentFact : Site → ValueFactId
  link : Site → Field → LiveTail.Link
  usedFacts : Finset ValueFactId
  usedOccurrences : Finset F1.Conditional.OccurrenceId
  loans : Finset Site
  permission : Site → Access
  dependencies : Finset F1.Conditional.Fact
  unknownAlias : Bool

def Typed (s : State) (i : Site) : Prop := ∃ c, s.cell i = some c ∧ c.phase = .typed
def DomainAlive (s : State) (i : Site) : Prop := ∃ c, s.cell i = some c ∧ c.domainLive = true

def FactLive (s : State) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) => ∃ i, Typed s i ∧
      ((p = parentPlace i ∧ vf = s.parentFact i) ∨
        ∃ f, p = fieldPlace i f ∧ vf = (s.link i f).currentFact)
  | .fixed (.domainLive d) => ∃ i, DomainAlive s i ∧ d = (s.origin i).domain
  | .occurrence o => ∃ i, Typed s i ∧ ∃ f, (s.link i f).occurrence = some o
  | .payloadValue o vf => ∃ i, Typed s i ∧ ∃ f,
      (s.link i f).occurrence = some o ∧ (s.link i f).payloadFact = some vf

def DependenciesValid (s : State) : Prop := ∀ f ∈ s.dependencies, FactLive s f

structure MemoryInvariant (s : State) : Prop where
  bounded : s.successes ≤ 5
  allocatedPrefix : ∀ i, (∃ c, s.cell i = some c) ↔ i.code < s.successes
  absent : ∀ i, s.cell i = none → s.owners i = [] ∧ s.claim i = none
  present : ∀ i c, s.cell i = some c →
    reconstruct s.world i (s.origin i) ∧ s.owners i = expectedOwners (s.origin i) c ∧
    s.claim i = expectedClaim (s.origin i) c ∧
    c.releases = (if c.phase = .released then 1 else 0) ∧
    (c.phase = .typed → c.domainLive = true) ∧
    (c.phase = .emptySlot → c.domainLive = true) ∧
    (c.phase = .released → c.domainLive = false)

structure FieldInvariant (s : State) : Prop where
  parentRecorded : ∀ i, Typed s i → s.parentFact i ∈ s.usedFacts
  fieldsRecorded : ∀ i, Typed s i → ∀ f, (s.link i f).currentFact ∈ s.usedFacts
  shape : ∀ i, Typed s i → ∀ f,
    (s.link i f).payload.isSome = (s.link i f).occurrence.isSome ∧
    (s.link i f).payload.isSome = (s.link i f).payloadFact.isSome
  occurrencesRecorded : ∀ i, Typed s i → ∀ f o, (s.link i f).occurrence = some o → o ∈ s.usedOccurrences
  payloadRecorded : ∀ i, Typed s i → ∀ f vf, (s.link i f).payloadFact = some vf → vf ∈ s.usedFacts
  occurrencesUnique : ∀ i j, Typed s i → Typed s j → ∀ f g o,
    (s.link i f).occurrence = some o → (s.link j g).occurrence = some o → i = j ∧ f = g

structure WellFormed (s : State) : Prop where
  memory : MemoryInvariant s
  fields : FieldInvariant s
  dependencies : DependenciesValid s

/-- Platform/source snapshot input is checked, not inferred from a Copy token.
The initial typed-root snapshot abstracts OneBacking->slot->initialize; it does
not prove an allocator, nominal completion or source frontend. -/
def allocatePost (s : State) (i : Site) (o : Origin) : State :=
  {s with
    successes := s.successes+1,
    origin := fun j => if j = i then o else s.origin j,
    cell := fun j => if j = i then some ⟨.typed,true,0⟩ else s.cell j,
    owners := fun j => if j = i then [.allocation o,.domain o] else s.owners j,
    claim := fun j => if j = i then some (.root ⟨0⟩ o.ptr.location (full o)) else s.claim j,
    parentFact := fun j => if j = i then initialParent i else s.parentFact j,
    link := fun j => if j = i then initialLink i else s.link j,
    usedFacts := s.usedFacts ∪ initialFacts i}

structure Allocate (s : State) (i : Site) (o : Origin) : Prop where
  pre : WellFormed s
  next : i.code = s.successes
  source : reconstruct s.world i o
  fresh : Disjoint (initialFacts i) s.usedFacts
  /-- Allocation failure paths occur before link wiring; no invented external observer. -/
  noObservers : s.dependencies = ∅

structure RootRef where
  world : LiveTail.WorldId
  ptr : PtrToken
  domain : DomainId
  mode : Access
  deriving DecidableEq, Repr
structure FieldRef where
  base : RootRef
  field : Field
  projection : ProjectionId
  deriving DecidableEq, Repr

def RootRefValid (s : State) (i : Site) (r : RootRef) : Prop :=
  r.world = s.world ∧ r.ptr = (s.origin i).ptr ∧ r.domain = (s.origin i).domain ∧
  Typed s i ∧ DomainAlive s i ∧ i ∈ s.loans ∧ AccessLe r.mode (s.permission i)
def FieldRefValid (s : State) (i : Site) (f : Field) (r : FieldRef) : Prop :=
  RootRefValid s i r.base ∧ r.field = f ∧ r.projection = projection f

/-- A copied locator preserves provenance; it grants neither A/D nor deref. -/
def Issued (s : State) (p : LiveTail.WorldId × PtrToken) : Prop :=
  p.1 = s.world ∧ ∃ i c, s.cell i = some c ∧ p.2 = (s.origin i).ptr

def Affected (s : State) (i : Site) (f : Field) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) =>
      (p = parentPlace i ∧ vf = s.parentFact i) ∨
      (p = fieldPlace i f ∧ vf = (s.link i f).currentFact)
  | .fixed (.domainLive _) => False
  | .occurrence o => (s.link i f).occurrence = some o
  | .payloadValue o vf => (s.link i f).occurrence = some o ∧ (s.link i f).payloadFact = some vf

def ChangeGuard (s : State) (i : Site) (f : Field) : Prop :=
  s.unknownAlias = false ∧ ∀ d ∈ s.dependencies, ¬ Affected s i f d
structure ChangePlan where
  parent : ValueFactId
  field : ValueFactId
  payload : ValueFactId
  occurrence : F1.Conditional.OccurrenceId

def ChangeFresh (s : State) (p : ChangePlan) : Prop :=
  p.parent ∉ s.usedFacts ∧ p.field ∉ s.usedFacts ∧ p.payload ∉ s.usedFacts ∧
  p.parent ≠ p.field ∧ p.parent ≠ p.payload ∧ p.field ≠ p.payload ∧ p.occurrence ∉ s.usedOccurrences

def changePost (s : State) (i : Site) (f : Field)
    (value : Option (LiveTail.WorldId × PtrToken)) (p : ChangePlan) : State :=
  {s with
    parentFact := fun j => if j = i then p.parent else s.parentFact j,
    link := fun j g => if j = i ∧ g = f then
      ⟨value,p.field,if value.isSome then some p.occurrence else none,
        if value.isSome then some p.payload else none⟩ else s.link j g,
    usedFacts := insert p.parent (insert p.field (insert p.payload s.usedFacts)),
    usedOccurrences := if value.isSome then insert p.occurrence s.usedOccurrences else s.usedOccurrences}

structure Replace (s : State) (i : Site) (f : Field) (r : FieldRef)
    (value : Option (LiveTail.WorldId × PtrToken)) (p : ChangePlan) : Prop where
  pre : WellFormed s
  ref : FieldRefValid s i f r
  write : r.base.mode.write = true
  incoming : ∀ ptr, value = some ptr → Issued s ptr
  fresh : ChangeFresh s p
  guard : ChangeGuard s i f

/-- Exact old field value (Copy Option<ptr>) is returned without occurrence data. -/
def oldResult (s : State) (i : Site) (f : Field) := (s.link i f).payload

/-- Existing uniform fact vocabulary determines every lifetime-ended blocker. -/
def EndGuard (s : State) (i : Site) : Prop :=
  s.unknownAlias = false ∧ i ∉ s.loans ∧ ∀ d ∈ s.dependencies,
    match d with
    | .fixed (.domainLive domain) => domain ≠ (s.origin i).domain
    | .fixed (.valueFact p _) => p ≠ parentPlace i ∧ ∀ f, p ≠ fieldPlace i f
    | .occurrence o => ∀ f, (s.link i f).occurrence ≠ some o
    | .payloadValue o _ => ∀ f, (s.link i f).occurrence ≠ some o

def endPost (s : State) (i : Site) : State :=
  {s with
    cell := fun j => if j = i then (s.cell i).map (fun c => {c with phase := .emptySlot}) else s.cell j,
    claim := fun j => if j = i then some (.slot ⟨0⟩ (full (s.origin i))) else s.claim j}
def erasePost (s : State) (i : Site) : State :=
  {s with
    cell := fun j => if j = i then (s.cell i).map (fun c => {c with phase := .raw}) else s.cell j,
    claim := fun j => if j = i then some (.storage (full (s.origin i))) else s.claim j}
def finalizePost (s : State) (i : Site) : State :=
  {s with
    cell := fun j => if j = i then (s.cell i).map (fun c => {c with domainLive := false}) else s.cell j,
    owners := fun j => if j = i then (s.owners i).filter (fun a => match a with | .domain _ => false | _ => true) else s.owners j}
def releasePost (s : State) (i : Site) : State :=
  {s with
    cell := fun j => if j = i then (s.cell i).map (fun c => {c with phase := .released,releases := c.releases+1}) else s.cell j,
    owners := fun j => if j = i then [] else s.owners j,
    claim := fun j => if j = i then none else s.claim j}
def cleanupPost (s : State) (i : Site) := releasePost (finalizePost (erasePost (endPost s i) i) i) i

def CanEnd (s : State) (i : Site) (d : Origin) : Prop :=
  Typed s i ∧ Authority.domain d ∈ s.owners i ∧ EndGuard s i
def CanErase (s : State) (i : Site) : Prop := ∃ c, s.cell i = some c ∧ c.phase = .emptySlot
def CanFinalize (s : State) (i : Site) (d : Origin) : Prop :=
  (∃ c, s.cell i = some c ∧ c.phase = .raw ∧ c.domainLive = true) ∧ Authority.domain d ∈ s.owners i
def CanRelease (s : State) (i : Site) (a : Origin) (raw : Extent) : Prop :=
  (∃ c, s.cell i = some c ∧ c.phase = .raw ∧ c.domainLive = false ∧ c.releases = 0) ∧
  Authority.allocation a ∈ s.owners i ∧ a = s.origin i ∧ raw = full a
structure Cleanup (s : State) (i : Site) (d a : Origin) (raw : Extent) : Prop where
  pre : WellFormed s
  endRoot : CanEnd s i d
  erase : CanErase (endPost s i) i
  finalize : CanFinalize (erasePost (endPost s i) i) i d
  release : CanRelease (finalizePost (erasePost (endPost s i) i) i) i a raw

end
end NewLang.Adjunct.FiveRoot
