import NewLang.F1.Occupancy.Lifetime
import NewLang.F1.Occupancy.Partition

namespace NewLang.F1.Relocation
open F0 Backing
noncomputable section

/-- Opaque value-owned annotations. Claim handles refer to the existing ledger;
this is not a new Allocation type, owner, or source-visible capability system. -/
structure PackageData where
  persistentPtrs : List PtrToken
  ownedClaims : Finset Occupancy.ClaimId
  opaqueAuthority : Nat

structure State where
  accounted : Occupancy.SumState
  data : PackageId → PackageData

structure WellFormed (g : Occupancy.Geometry) (layout : Occupancy.Layout) (s : State) : Prop
    extends Occupancy.SumWellFormed g layout s.accounted where
  ownedPresent : ∀ p, Conditional.Survives s.accounted.base.semantic p → ∀ id ∈ (s.data p).ownedClaims,
    id ∈ s.accounted.ledger.active ∧ (s.accounted.ledger.claim id).valueOwned = true
  ownedUnique : ∀ p q, Conditional.Survives s.accounted.base.semantic p → Conditional.Survives s.accounted.base.semantic q →
    p ≠ q → Disjoint (s.data p).ownedClaims (s.data q).ownedClaims

/-- Existing token identities; provenance is not a blocking dependency. -/
def CurrentToken (s : State) (p : PtrToken) : Prop :=
  p.location ∈ s.accounted.base.semantic.liveRoots ∧
  (s.accounted.base.semantic.root p.location).incarnation = p.incarnation

/-- A governing relation is identified by its root incarnation and domain,
not by a value-owned independently transferable relation identifier. -/
def governingKey (s : State) (l : RootLocationId) : IncarnationId × DomainId :=
  ((s.accounted.base.semantic.root l).incarnation,(s.accounted.base.semantic.root l).governing)

structure Conditions where
  identified : Prop
  aligned : Prop
  prepared : Prop
  canEnd : DomainId → Prop

/-- Only distinct-place allocation has freshness inputs. Returns are existing
Storage carriers, with finite exact raw footprint, not a persistent raw-range API. -/
structure Move where
  source : RootLocationId
  destination : RootLocationId
  sourceClaim : Occupancy.ClaimId
  newRootClaim : Occupancy.ClaimId
  type : Occupancy.TypeId
  sourceExtent : Occupancy.Extent
  destinationExtent : Occupancy.Extent
  inputRaw : Finset Occupancy.ClaimId
  outputRaw : Finset Occupancy.ClaimId
  rawExtent : Occupancy.ClaimId → Occupancy.Extent
  incarnation : IncarnationId
  allocation : Conditional.Allocation

def sourceBytes (g : Occupancy.Geometry) (m : Move) := m.sourceExtent.footprint g
def destinationBytes (g : Occupancy.Geometry) (m : Move) := m.destinationExtent.footprint g

def movedRoot (sites : RootSiteLayout) (s : Conditional.State) (m : Move) : Conditional.SumRoot :=
  { Conditional.installRoot (s.root m.source) (s.root m.source).package m.allocation with
    place := sites.placeAt m.destination,incarnation := m.incarnation }

def semanticCandidate (sites : RootSiteLayout) (s : Conditional.State) (m : Move) : Conditional.State :=
  {s with
    liveRoots := insert m.destination (s.liveRoots.erase m.source)
    root := fun l => if l = m.destination then movedRoot sites s m else s.root l
    usedValueFacts := s.usedValueFacts ∪ m.allocation.facts
    usedIncarnations := insert m.incarnation s.usedIncarnations
    usedOccurrences := s.usedOccurrences ∪ m.allocation.occurrences }

def physicalCandidate (g : Occupancy.Geometry) (s : PhysicalState) (m : Move) : PhysicalState :=
  startPlacement (endPlacement s m.source) m.destination (m.destinationExtent.placement g)

def ledgerCandidate (s : Occupancy.Ledger) (m : Move) : Occupancy.Ledger :=
  {s with
    active := insert m.newRootClaim ((s.active.erase m.sourceClaim \ m.inputRaw) ∪ m.outputRaw)
    claim := fun id => if id = m.newRootClaim then .root m.type m.destination m.destinationExtent
      else if id ∈ m.outputRaw then .storage (m.rawExtent id) else s.claim id }

def candidate (g : Occupancy.Geometry) (sites : RootSiteLayout) (s : State) (m : Move) : State :=
  ⟨⟨⟨semanticCandidate sites s.accounted.base.semantic m,physicalCandidate g s.accounted.base.physical m⟩,
    ledgerCandidate s.accounted.ledger m⟩,s.data⟩

/-- Receipt is a proof observation of fresh state/provenance, not a final source
return spelling or a value-owned governing relation. -/
inductive Receipt where
  | identity
  | moved : PtrToken → (IncarnationId × DomainId) → Receipt
  deriving DecidableEq

def moveReceipt (s : State) (m : Move) : Receipt :=
  .moved ⟨m.destination,m.incarnation⟩ ⟨m.incarnation,(s.accounted.base.semantic.root m.source).governing⟩

structure RawMove (g : Occupancy.Geometry) (sites : RootSiteLayout) (ctx : Conditions)
    (s : State) (m : Move) (receipt : Receipt) (post : State) : Prop where
  identified : ctx.identified
  sourceLive : m.source ∈ s.accounted.base.semantic.liveRoots
  sourceClaimPresent : Occupancy.Has s.accounted.ledger m.sourceClaim (.root m.type m.source m.sourceExtent)
  sourceSite : (s.accounted.base.semantic.root m.source).place = sites.placeAt m.source
  sourceValue : ∃ v, s.accounted.base.semantic.values (s.accounted.base.semantic.root m.source).package = some (.sum v) ∧
    Conditional.FitsAllocation v m.allocation
  differentExtent : m.sourceExtent ≠ m.destinationExtent
  differentLocation : m.source ≠ m.destination
  destinationVacant : m.destination ∉ s.accounted.base.semantic.liveRoots
  destinationLiveBacking : m.destinationExtent.region ∈ s.accounted.base.physical.world.liveRegions
  destinationFits : m.destinationExtent.Fits g
  exactSize : m.destinationExtent.range.length = m.sourceExtent.range.length
  alignment : ctx.aligned
  ending : ctx.canEnd (s.accounted.base.semantic.root m.source).governing
  prepared : ctx.prepared
  sourceRead : (s.accounted.base.physical.world.access m.sourceExtent.region).read = true
  destinationWrite : (s.accounted.base.physical.world.access m.destinationExtent.region).write = true
  rawInputs : ∀ id ∈ m.inputRaw, ∃ e, Occupancy.Has s.accounted.ledger id (.storage e)
  inputCoverage : m.inputRaw.biUnion (fun id => (s.accounted.ledger.claim id).extent.footprint g) =
    destinationBytes g m \ sourceBytes g m
  outputCoverage : m.outputRaw.biUnion (fun id => (m.rawExtent id).footprint g) =
    sourceBytes g m \ destinationBytes g m
  outputPositive : ∀ id ∈ m.outputRaw, 0 < (m.rawExtent id).range.length
  outputDisjoint : ∀ i ∈ m.outputRaw, ∀ j ∈ m.outputRaw, i ≠ j →
    Disjoint ((m.rawExtent i).footprint g) ((m.rawExtent j).footprint g)
  outputFresh : ∀ id ∈ m.outputRaw, id ∉ s.accounted.ledger.active
  rootFresh : m.newRootClaim ∉ s.accounted.ledger.active
  rootNotRaw : m.newRootClaim ∉ m.outputRaw
  freshIncarnation : m.incarnation ∉ s.accounted.base.semantic.usedIncarnations
  freshFacts : Conditional.FreshAllocation s.accounted.base.semantic m.allocation
  post_eq : post = candidate g sites s m
  receipt_eq : receipt = moveReceipt s m

inductive Action where
  | same : RootLocationId → Occupancy.ClaimId → Occupancy.TypeId → Occupancy.Extent → Action
  | move : Move → Action

/-- Only complete pre/post states. Same has no fresh/ending/read/write premises. -/
inductive RawRelocate (g : Occupancy.Geometry) (sites : RootSiteLayout) (ctx : Conditions) :
    State → Action → Receipt → State → Prop where
  | same {s l id t e} : ctx.identified → l ∈ s.accounted.base.semantic.liveRoots →
      Occupancy.Has s.accounted.ledger id (.root t l e) → RawRelocate g sites ctx s (.same l id t e) .identity s
  | move {s m receipt post} : RawMove g sites ctx s m receipt post →
      RawRelocate g sites ctx s (.move m) receipt post

def Step (g : Occupancy.Geometry) (layout : Occupancy.Layout) (sites : RootSiteLayout) (ctx : Conditions)
    (s : State) (action : Action) (receipt : Receipt) (post : State) : Prop :=
  WellFormed g layout s ∧ RawRelocate g sites ctx s action receipt post ∧ WellFormed g layout post

theorem wellFormed_erases_to_accounting {g layout s} (wf : WellFormed g layout s) :
    Occupancy.SumWellFormed g layout s.accounted := wf.toSumWellFormed

theorem wellFormed_erases_to_backing {g layout s} (wf : WellFormed g layout s) :
    Backing.SumWellFormed s.accounted.base := Occupancy.sum_wellFormed_erases_to_backing wf.toSumWellFormed

theorem wellFormed_erases_to_conditional {g layout s} (wf : WellFormed g layout s) :
    Conditional.WellFormed s.accounted.base.semantic := Occupancy.sum_wellFormed_erases_to_conditional wf.toSumWellFormed

theorem wellFormed_erases_to_current {g layout s} (wf : WellFormed g layout s) :
    F1.CurrentWellFormed (Conditional.erase s.accounted.base.semantic) := Occupancy.sum_wellFormed_erases_to_current wf.toSumWellFormed

theorem wellFormed_erases_to_f0 {g layout s} (wf : WellFormed g layout s) :
    F0.WellFormed (F1.eraseToF0 (Conditional.erase s.accounted.base.semantic).base) :=
  Occupancy.sum_wellFormed_erases_to_f0 wf.toSumWellFormed

end
end NewLang.F1.Relocation
