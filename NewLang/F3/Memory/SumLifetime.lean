import NewLang.F1.Occupancy.Lifetime

namespace NewLang.F3.Memory.SumLifetime
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Ordinary-fact view, using the reviewed dependency-dropping projection.
This view is never the authority for rich transition legality. -/
def coarse (s : F1.Conditional.State) : F0.State where
  occupancy := fun l => if l ∈ s.liveRoots then
    .live ⟨(s.root l).place, (s.root l).incarnation, (s.root l).currentFact,
      (s.root l).package, (s.root l).governing⟩ else .vacant
  packages := fun p => (s.values p).map (fun v => ⟨F1.Conditional.projectFacts v.dependencies, v.discardable s⟩)
  loosePackages := s.loosePackages
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := s.usedValueFacts
  usedIncarnations := s.usedIncarnations

def coarseRoot (r : F1.Conditional.SumRoot) : LiveRoot :=
  ⟨r.place,r.incarnation,r.currentFact,r.package,r.governing⟩

def coarseState (s : F1.Occupancy.SumState) : F1.Occupancy.State :=
  ⟨⟨coarse s.base.semantic,s.base.physical⟩,s.ledger⟩

/-- Exactly the facts this bounded one-root lifetime ending invalidates.
Domains remain live; persistent provenance is not automatically a dependency. -/
def Ended (r : F1.Conditional.SumRoot) : F1.Conditional.Fact → Prop
  | .fixed (.valueFact p vf) => p = r.place ∧ vf = r.currentFact
  | .fixed (.domainLive _) => False
  | .occurrence o => r.occurrence = some o
  | .payloadValue o vf => r.occurrence = some o ∧ r.payloadFact = some vf

def remainingCarriers (s : F1.Conditional.State) (l : RootLocationId) (returned : Bool) : Finset PackageId :=
  if returned then insert (s.root l).package s.loosePackages else s.loosePackages.erase (s.root l).package

/-- Local ended-fact conflict check over the actual remaining carriers.
It neither demands post WellFormed nor reconstructs dependencies from erasure. -/
def SurvivorGuard (s : F1.Conditional.State) (l : RootLocationId) (returned : Bool) : Prop :=
  ∀ p ∈ remainingCarriers s l returned, ∀ v, s.values p = some v →
    ∀ f ∈ v.dependencies, ¬ Ended (s.root l) f

/-- Used only under the single-live-root premise. Inactive root records are inert.
Package data, types, domains and all historical identity sets are unchanged. -/
def endSemantic (s : F1.Conditional.State) (l : RootLocationId) (returned : Bool) : F1.Conditional.State :=
  {s with liveRoots := ∅, loosePackages := remainingCarriers s l returned}

def endCandidate (s : F1.Occupancy.SumState) (l : RootLocationId) (source result : ClaimId)
    (t : TypeId) (e : Extent) (returned : Bool) : F1.Occupancy.SumState :=
  ⟨⟨endSemantic s.base.semantic l returned,endPlacement s.base.physical l⟩,
    consumeOne s.ledger source result (.slot t e)⟩

/-- Deliberately bounded: one live sum root, one exact responsible claim, one
explicit region. Loose external semantic survivors are permitted. `ce` stands
only for caller ending/representation authority, not whole-operation safety. -/
structure EndingInput (ce : Prop) (s : F1.Occupancy.SumState) (l : RootLocationId)
    (source result : ClaimId) (t : TypeId) (e : Extent) (d : DomainId) (ptr : AccessPtr) : Prop where
  singleRoot : s.base.semantic.liveRoots = {l}
  singleRegion : s.ledger.scope = {e.region}
  singleClaim : s.ledger.active = {source}
  sourceClaim : Has s.ledger source (.root t l e)
  resultFresh : result ∉ s.ledger.active
  endingAllowed : ce
  domainMatches : d = (s.base.semantic.root l).governing
  token : ptr.token = ⟨l,(s.base.semantic.root l).incarnation⟩
  current : CurrentAccessPtr (coarseState s).flat ptr

structure RawTake (ce : Prop) (s : F1.Occupancy.SumState) (l : RootLocationId)
    (source result : ClaimId) (t : TypeId) (e : Extent) (d : DomainId)
    (ptr : AccessPtr) (post : F1.Occupancy.SumState) : Prop where
  input : EndingInput ce s l source result t e d ptr
  read : ptr.evidence.access.read = true
  post_eq : post = endCandidate s l source result t e true

structure RawDestroy (ce : Prop) (s : F1.Occupancy.SumState) (l : RootLocationId)
    (source result : ClaimId) (t : TypeId) (e : Extent) (d : DomainId)
    (ptr : AccessPtr) (post : F1.Occupancy.SumState) : Prop where
  input : EndingInput ce s l source result t e d ptr
  discardable : ∃ v, s.base.semantic.values (s.base.semantic.root l).package = some v ∧
    v.discardable s.base.semantic = true
  post_eq : post = endCandidate s l source result t e false

def TakeStep (g : Geometry) (layout : Layout) (ce : Prop) (s : F1.Occupancy.SumState) (l : RootLocationId)
    (source result : ClaimId) (t : TypeId) (e : Extent) (d : DomainId)
    (ptr : AccessPtr) (post : F1.Occupancy.SumState) : Prop :=
  SumWellFormed g layout s ∧ RawTake ce s l source result t e d ptr post ∧
    SurvivorGuard s.base.semantic l true

def DestroyStep (g : Geometry) (layout : Layout) (ce : Prop) (s : F1.Occupancy.SumState) (l : RootLocationId)
    (source result : ClaimId) (t : TypeId) (e : Extent) (d : DomainId)
    (ptr : AccessPtr) (post : F1.Occupancy.SumState) : Prop :=
  SumWellFormed g layout s ∧ RawDestroy ce s l source result t e d ptr post ∧
    SurvivorGuard s.base.semantic l false

end
end NewLang.F3.Memory.SumLifetime
