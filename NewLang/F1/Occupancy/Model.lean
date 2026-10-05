import NewLang.F1.Occupancy.Range

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

/-- Static type/layout key, not a source-visible owner type. -/
structure TypeId where
  index : Nat
  deriving DecidableEq, Repr

structure Layout where
  size : TypeId → Nat
  positive : ∀ t, 0 < size t

/-- Ghost handles for current authority carriers. Not historical object identity;
reusing an inactive handle is allowed, unlike incarnation/fact reuse. -/
structure ClaimId where
  index : Nat
  deriving DecidableEq, Repr

/-- Raw/empty claims are value-owned. A live claim is the accounting view of the
same state-owned root placement, not a second independently owned authority. -/
inductive Claim where
  | storage : Extent → Claim
  | slot : TypeId → Extent → Claim
  | root : TypeId → RootLocationId → Extent → Claim
  deriving DecidableEq, Repr

def Claim.extent : Claim → Extent
  | .storage e | .slot _ e | .root _ _ e => e

def Claim.valueOwned : Claim → Bool
  | .storage _ | .slot _ _ => true
  | .root _ _ _ => false

/-- Occupancy responsibility cannot be copied or silently discarded, even when
its current T semantic value is Discardable. Destroy returns empty responsibility. -/
def Claim.copyable (_ : Claim) : Bool := false
def Claim.discardable (_ : Claim) : Bool := false

structure Ledger where
  /-- Fixed proof accounting scope, not Allocation/deallocation authority. -/
  scope : Finset BackingRegionId
  active : Finset ClaimId
  claim : ClaimId → Claim

def Has (s : Ledger) (id : ClaimId) (claim : Claim) : Prop := id ∈ s.active ∧ s.claim id = claim

def TotalFootprint (g : Geometry) (s : Ledger) : Finset AbstractByteId :=
  s.active.biUnion (fun id => (s.claim id).extent.footprint g)

def ExpectedFootprint (p : PhysicalState) (s : Ledger) : Finset AbstractByteId :=
  s.scope.biUnion p.world.bytes

def NoOverlap (g : Geometry) (s : Ledger) : Prop :=
  ∀ a ∈ s.active, ∀ b ∈ s.active, a ≠ b →
    Disjoint ((s.claim a).extent.footprint g) ((s.claim b).extent.footprint g)

/-- One accounting for raw, empty and live responsibility. Complete coverage is
only for the explicit scoped regions, with no allocator/dynamic owner algebra. -/
def Claim.Typed (layout : Layout) : Claim → Prop
  | .storage _ => True
  | .slot t e | .root t _ e => e.range.length = layout.size t

structure AccountingShape (g : Geometry) (layout : Layout) (live : RootLocationId → Prop)
    (p : PhysicalState) (s : Ledger) : Prop where
  geometry : g.Compatible p.world
  regions : RegionsDisjoint p.world
  scopeLive : ∀ r ∈ s.scope, r ∈ p.world.liveRegions
  inScope : ∀ id ∈ s.active, (s.claim id).extent.region ∈ s.scope
  positive : ∀ id ∈ s.active, 0 < (s.claim id).extent.range.length
  fits : ∀ id ∈ s.active, (s.claim id).extent.Fits g
  typed : ∀ id ∈ s.active, (s.claim id).Typed layout
  roots : ∀ l, live l ↔ ∃ id ∈ s.active, ∃ t e, s.claim id = .root t l e
  placements : ∀ l pl, p.placement l = some pl ↔
    ∃ id ∈ s.active, ∃ t e, s.claim id = .root t l e ∧ e.placement g = pl


structure Accounting (g : Geometry) (layout : Layout) (live : RootLocationId → Prop)
    (p : PhysicalState) (s : Ledger) : Prop extends AccountingShape g layout live p s where
  disjoint : NoOverlap g s
  coverage : TotalFootprint g s = ExpectedFootprint p s

structure State where
  flat : Backing.FlatState
  ledger : Ledger

/-- Inherited semantic obligations are explicit. Physical validity is derived
from the claim accounting, not assumed as an erased-WF premise. -/
structure WellFormed (g : Geometry) (layout : Layout) (s : State) : Prop extends F0.WellFormed s.flat.semantic where
  accounting : Accounting g layout (FlatLive s.flat.semantic) s.flat.physical s.ledger

/-- Accounting can also refine the existing conditional sum slice without
changing its precise dependency invariant or implementing sum lifetime start. -/
structure SumState where
  base : Backing.SumState
  ledger : Ledger

structure SumWellFormed (g : Geometry) (layout : Layout) (s : SumState) : Prop extends Conditional.Invariant s.base.semantic where
  dependencies : Conditional.DependenciesValid s.base.semantic
  accounting : Accounting g layout (fun l => l ∈ s.base.semantic.liveRoots) s.base.physical s.ledger

theorem accounting_derives_physical_wellFormed {g layout live p s} (wf : Accounting g layout live p s) :
    PhysicalWellFormed live p := by
  constructor
  · exact wf.regions
  · intro l; constructor
    · intro live
      rcases (wf.roots l).mp live with ⟨id,active,t,e,claim⟩
      exact ⟨e.placement g,(wf.placements l _).mpr ⟨id,active,t,e,claim,rfl⟩⟩
    · rintro ⟨pl,placed⟩
      rcases (wf.placements l pl).mp placed with ⟨id,active,t,e,claim,_⟩
      exact (wf.roots l).mpr ⟨id,active,t,e,claim⟩
  · intro l pl placed
    rcases (wf.placements l pl).mp placed with ⟨id,active,t,e,claim,rfl⟩
    have scopeMember := wf.inScope id active
    rw [claim] at scopeMember
    exact wf.scopeLive e.region scopeMember
  · intro l pl placed
    rcases (wf.placements l pl).mp placed with ⟨id,active,t,e,claim,rfl⟩
    have fits := wf.fits id active
    rw [claim] at fits
    exact fitting_extent_is_inside_backing wf.geometry fits
  · intro l m a b la mb different
    rcases (wf.placements l a).mp la with ⟨i,ia,t,e,ic,rfl⟩
    rcases (wf.placements m b).mp mb with ⟨j,ja,u,f,jc,rfl⟩
    have ids : i ≠ j := by
      intro same; subst j
      exact different (Claim.root.inj (ic.symm.trans jc)).2.1
    have disjoint := wf.disjoint i ia j ja ids
    simpa only [ic,jc,Claim.extent,Extent.placement] using disjoint

theorem wellFormed_erases_to_backing {g : Geometry} {layout : Layout} {s : State} (wf : WellFormed g layout s) :
    Backing.FlatWellFormed s.flat :=
  ⟨⟨wf.carrierUnique,wf.placesUnique,wf.incarnationsUnique,wf.packagesPresent,wf.domainsValid,
    wf.dependenciesValid,wf.valueFactsRecorded,wf.incarnationsRecorded,wf.domainCarrierCoherent⟩,
    accounting_derives_physical_wellFormed wf.accounting⟩

theorem wellFormed_erases_to_f0 {g : Geometry} {layout : Layout} {s : State} (wf : WellFormed g layout s) :
    F0.WellFormed s.flat.semantic :=
  Backing.flat_wellFormed_erases_to_f0 (wellFormed_erases_to_backing wf)

theorem sum_wellFormed_erases_to_backing {g : Geometry} {layout : Layout} {s : SumState} (wf : SumWellFormed g layout s) :
    Backing.SumWellFormed s.base :=
  ⟨wf.toInvariant,wf.dependencies,accounting_derives_physical_wellFormed wf.accounting⟩

theorem sum_wellFormed_erases_to_conditional {g : Geometry} {layout : Layout} {s : SumState} (wf : SumWellFormed g layout s) :
    Conditional.WellFormed s.base.semantic :=
  Backing.sum_wellFormed_erases_to_conditional (sum_wellFormed_erases_to_backing wf)

theorem sum_wellFormed_erases_to_current {g : Geometry} {layout : Layout} {s : SumState} (wf : SumWellFormed g layout s) :
    F1.CurrentWellFormed (Conditional.erase s.base.semantic) :=
  Backing.sum_wellFormed_erases_to_current (sum_wellFormed_erases_to_backing wf)

theorem sum_wellFormed_erases_to_f0 {g : Geometry} {layout : Layout} {s : SumState} (wf : SumWellFormed g layout s) :
    F0.WellFormed (F1.eraseToF0 (Conditional.erase s.base.semantic).base) :=
  Backing.sum_wellFormed_erases_to_f0 (sum_wellFormed_erases_to_backing wf)

theorem surviving_claim_requires_live_backing {g layout live p s} (wf : Accounting g layout live p s)
    {id : ClaimId} (active : id ∈ s.active) : (s.claim id).extent.region ∈ p.world.liveRegions :=
  wf.scopeLive _ (wf.inScope id active)

theorem every_scoped_byte_has_unique_responsibility {g layout live p s} (wf : Accounting g layout live p s)
    {byte : AbstractByteId} (covered : byte ∈ ExpectedFootprint p s) :
    ∃! id, id ∈ s.active ∧ byte ∈ (s.claim id).extent.footprint g := by
  rw [← wf.coverage] at covered
  rcases Finset.mem_biUnion.mp covered with ⟨id,active,member⟩
  refine ⟨id,⟨active,member⟩,?_⟩
  rintro other ⟨oa,om⟩
  by_contra different
  exact (Finset.disjoint_left.mp (wf.disjoint other oa id active different)) om member

theorem nonempty_claim_cannot_be_covered_twice {g layout live p s} (wf : Accounting g layout live p s)
    {a b : ClaimId} (aa : a ∈ s.active) (ba : b ∈ s.active) (different : a ≠ b)
    (included : (s.claim a).extent.footprint g ⊆ (s.claim b).extent.footprint g) : False := by
  rcases extent_footprint_nonempty g (wf.positive a aa) with ⟨byte,member⟩
  exact (Finset.disjoint_left.mp (wf.disjoint a aa b ba different)) member (included member)

theorem full_region_storage_excludes_outstanding_subclaim {g layout live p s} (wf : Accounting g layout live p s)
    {id other : ClaimId} {e : Extent} (full : Has s id (.storage e))
    (range : e.range = ⟨0,g.capacity e.region⟩) (oa : other ∈ s.active) (different : other ≠ id)
    (sameRegion : (s.claim other).extent.region = e.region) : False := by
  apply nonempty_claim_cannot_be_covered_twice wf oa full.1 different
  have whole : e.footprint g = p.world.bytes e.region := by
    rw [wf.geometry e.region]
    simp [Extent.footprint,range,Range.positions,Range.finish]
  rw [full.2,Claim.extent,whole,← sameRegion]
  exact fitting_extent_is_inside_backing wf.geometry (wf.fits other oa)

theorem storage_is_affine_nonDiscardable (e : Extent) :
    (Claim.storage e).valueOwned = true ∧ (Claim.storage e).copyable = false ∧
    (Claim.storage e).discardable = false := ⟨rfl,rfl,rfl⟩

theorem slot_is_empty_authority_not_live_value (t : TypeId) (e : Extent) :
    (Claim.slot t e).valueOwned = true ∧ (Claim.slot t e).copyable = false ∧
    (Claim.slot t e).discardable = false ∧ ∀ u l f, Claim.slot t e ≠ Claim.root u l f := by
  exact ⟨rfl,rfl,rfl,by intros; simp⟩

end
end NewLang.F1.Occupancy
