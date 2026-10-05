import NewLang.F1.Conditional.Proofs
import NewLang.F0.Reference
import NewLang.F1.Erasure

namespace NewLang.F1.Backing
open F0
noncomputable section

/-- Nominal backing identity, unrelated to machine addresses. -/
structure BackingRegionId where
  index : Nat
  deriving DecidableEq, Repr

/-- Opaque abstract backing-byte instance, not a numeric address or offset. -/
structure AbstractByteId where
  index : Nat
  deriving DecidableEq, Repr

structure Access where
  read : Bool
  write : Bool
  deriving DecidableEq, Repr

def AccessLe (requested available : Access) : Prop :=
  (requested.read = true → available.read = true) ∧
  (requested.write = true → available.write = true)

structure World where
  liveRegions : Finset BackingRegionId
  bytes : BackingRegionId → Finset AbstractByteId
  access : BackingRegionId → Access

/-- Draft 17.8 §3.1: independent live regions cannot alias abstract bytes. -/
def RegionsDisjoint (w : World) : Prop :=
  ∀ r ∈ w.liveRegions, ∀ q ∈ w.liveRegions, r ≠ q → Disjoint (w.bytes r) (w.bytes q)

/-- Exact occupied extent in one region; geometric contiguity/alignment/type-fit
remain explicit caller responsibilities. No allocator or Storage claim is encoded. -/
structure Placement where
  region : BackingRegionId
  occupied : Finset AbstractByteId
  deriving DecidableEq

structure PhysicalState where
  world : World
  placement : RootLocationId → Option Placement

/-- Root placements only. Fixed subobjects may overlap their enclosing root;
this predicate does not impose disjointness between ancestors and descendants. -/
structure PhysicalWellFormed (live : RootLocationId → Prop) (p : PhysicalState) : Prop where
  regions : RegionsDisjoint p.world
  exact : ∀ l, live l ↔ ∃ placement, p.placement l = some placement
  regionLive : ∀ l pl, p.placement l = some pl → pl.region ∈ p.world.liveRegions
  extent : ∀ l pl, p.placement l = some pl → pl.occupied ⊆ p.world.bytes pl.region
  rootsDisjoint : ∀ l m a b, p.placement l = some a → p.placement m = some b →
    l ≠ m → Disjoint a.occupied b.occupied

structure Evidence where
  region : BackingRegionId
  access : Access
  deriving DecidableEq, Repr

def EvidenceValid (w : World) (e : Evidence) : Prop :=
  e.region ∈ w.liveRegions ∧ AccessLe e.access (w.access e.region)

def WriteAt (p : PhysicalState) (l : RootLocationId) : Prop :=
  ∃ pl, p.placement l = some pl ∧ (p.world.access pl.region).write = true

/-- Conservative extension of the conditional sum slice, with the original
semantic obligations stated explicitly, not an erased-WF assumption. -/
structure SumState where
  semantic : Conditional.State
  physical : PhysicalState

structure SumWellFormed (s : SumState) : Prop extends Conditional.Invariant s.semantic where
  dependencies : Conditional.DependenciesValid s.semantic
  backing : PhysicalWellFormed (fun l => l ∈ s.semantic.liveRoots) s.physical

/-- A separate flat lifetime slice reuses reviewed F0 lifetime rules. This is not
an implementation of sum initialization or Storage/slot ownership. -/
structure FlatState where
  semantic : F0.State
  physical : PhysicalState

def FlatLive (s : F0.State) (l : RootLocationId) : Prop :=
  ∃ r, s.occupancy l = .live r

structure FlatWellFormed (s : FlatState) : Prop extends F0.WellFormed s.semantic where
  backing : PhysicalWellFormed (FlatLive s.semantic) s.physical

structure AccessPtr where
  token : PtrToken
  evidence : Evidence

def CurrentAccessPtr (s : FlatState) (ptr : AccessPtr) : Prop :=
  CurrentPtr s.semantic ptr.token ∧ EvidenceValid s.physical.world ptr.evidence ∧
  ∃ pl, s.physical.placement ptr.token.location = some pl ∧ pl.region = ptr.evidence.region

theorem accessLe_refl (a : Access) : AccessLe a a := ⟨id, id⟩

theorem accessLe_trans {a b c : Access} (ab : AccessLe a b) (bc : AccessLe b c) : AccessLe a c :=
  ⟨fun h => bc.1 (ab.1 h), fun h => bc.2 (ab.2 h)⟩

theorem evidence_cannot_amplify_read {w : World} {e : Evidence}
    (valid : EvidenceValid w e) (readable : e.access.read = true) :
    (w.access e.region).read = true := valid.2.1 readable

theorem evidence_cannot_amplify_write {w : World} {e : Evidence}
    (valid : EvidenceValid w e) (writable : e.access.write = true) :
    (w.access e.region).write = true := valid.2.2 writable

theorem sum_wellFormed_erases_to_conditional {s : SumState} (wf : SumWellFormed s) :
    Conditional.WellFormed s.semantic := ⟨wf.toInvariant, wf.dependencies⟩

theorem sum_wellFormed_erases_to_current {s : SumState} (wf : SumWellFormed s) :
    F1.CurrentWellFormed (Conditional.erase s.semantic) :=
  Conditional.wellFormed_erases_to_currentWellFormed (sum_wellFormed_erases_to_conditional wf)

theorem sum_wellFormed_erases_to_f0 {s : SumState} (wf : SumWellFormed s) :
    F0.WellFormed (F1.eraseToF0 (Conditional.erase s.semantic).base) :=
  F1.f1_wellFormed_erases_to_f0_wellFormed (sum_wellFormed_erases_to_current wf).structural

theorem flat_wellFormed_erases_to_f0 {s : FlatState} (wf : FlatWellFormed s) :
    F0.WellFormed s.semantic :=
  ⟨wf.carrierUnique, wf.placesUnique, wf.incarnationsUnique, wf.packagesPresent,
    wf.domainsValid, wf.dependenciesValid, wf.valueFactsRecorded,
    wf.incarnationsRecorded, wf.domainCarrierCoherent⟩

theorem live_root_requires_live_region {live : RootLocationId → Prop} {p : PhysicalState}
    (wf : PhysicalWellFormed live p) {l : RootLocationId} (rootLive : live l) :
    ∃ pl, p.placement l = some pl ∧ pl.region ∈ p.world.liveRegions := by
  rcases (wf.exact l).mp rootLive with ⟨pl, placed⟩
  exact ⟨pl, placed, wf.regionLive l pl placed⟩

theorem dead_region_cannot_back_live_root {live : RootLocationId → Prop} {p : PhysicalState}
    (wf : PhysicalWellFormed live p) {l : RootLocationId} {pl : Placement}
    (placed : p.placement l = some pl) (dead : pl.region ∉ p.world.liveRegions) : False :=
  dead (wf.regionLive l pl placed)

end
end NewLang.F1.Backing
