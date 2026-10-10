import NewLang.Adjunct.OneBackingIssuerBoundary
import Mathlib.Data.Finset.Card

/-! Issue #53. Adjunct introduction of the ALREADY SELECTED trusted issuer law.
This constructs a post-state; it is not an accepted-core transition or a native
allocator proof. Environmental input contains bytes/freshness, NEVER a grant. -/
namespace NewLang.Adjunct.OneBackingIssuerRich
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Ghost resource supply for ONE positive allocation. `claim` is a fresh proof
handle, not a preexisting source Storage. No Allocation, Domain or root supplied. -/
structure Supply (g : Geometry) (s : F1.Occupancy.State) where
  region : BackingRegionId
  claim : ClaimId
  n : Nat
  positive : 0 < n
  byteAt : Nat → AbstractByteId
  injective : Function.Injective byteAt
  freshRegion : region ∉ s.flat.physical.world.liveRegions
  freshClaim : claim ∉ s.ledger.active
  disjoint : ∀ r ∈ s.flat.physical.world.liveRegions,
    Disjoint ((Finset.range n).image byteAt) (s.flat.physical.world.bytes r)

def geometry {g s} (a : Supply g s) : Geometry where
  capacity r := if r = a.region then a.n else g.capacity r
  byteAt r := if r = a.region then a.byteAt else g.byteAt r
  injective r := by split <;> [exact a.injective; exact g.injective r]

def extent {g s} (a : Supply g s) : Extent := ⟨a.region,⟨0,a.n⟩⟩

def world {g s} (a : Supply g s) : World where
  liveRegions := insert a.region s.flat.physical.world.liveRegions
  bytes r := if r = a.region then (Finset.range a.n).image a.byteAt
    else s.flat.physical.world.bytes r
  access r := if r = a.region then ⟨true,true⟩ else s.flat.physical.world.access r

def ledger {g s} (a : Supply g s) : Ledger where
  scope := insert a.region s.ledger.scope
  active := insert a.claim s.ledger.active
  claim id := if id = a.claim then .storage (extent a) else s.ledger.claim id

def post {g s} (a : Supply g s) : F1.Occupancy.State where
  flat := ⟨s.flat.semantic,⟨world a,s.flat.physical.placement⟩⟩
  ledger := ledger a

theorem old_region_ne {g layout s} (_wf : WellFormed g layout s)
    (a : Supply g s) {r} (live : r ∈ s.flat.physical.world.liveRegions) : r ≠ a.region := by
  intro eq; subst r; exact a.freshRegion live

theorem old_claim_region_ne {g layout s} (wf : WellFormed g layout s)
    (a : Supply g s) {id} (active : id ∈ s.ledger.active) :
    (s.ledger.claim id).extent.region ≠ a.region :=
  old_region_ne wf a (surviving_claim_requires_live_backing wf.accounting active)

theorem footprint_frame {g s} (a : Supply g s) {e : Extent}
    (ne : e.region ≠ a.region) : e.footprint (geometry a) = e.footprint g := by
  simp [Extent.footprint,geometry,ne]

theorem full_footprint {g s} (a : Supply g s) :
    (extent a).footprint (geometry a) = (Finset.range a.n).image a.byteAt := by
  simp [Extent.footprint,extent,geometry,Range.positions,Range.finish]

theorem full_has {g s} (a : Supply g s) :
    Has (post a).ledger a.claim (.storage (extent a)) := by simp [Has,post,ledger]

theorem old_claim_frame {g s} (a : Supply g s) {id} (active : id ∈ s.ledger.active) :
    (post a).ledger.claim id = s.ledger.claim id := by
  have ne : id ≠ a.claim := by intro eq; subst id; exact a.freshClaim active
  simp [post,ledger,ne]

theorem old_world_frame {g layout s} (wf : WellFormed g layout s) (a : Supply g s)
    {r} (live : r ∈ s.flat.physical.world.liveRegions) :
    (post a).flat.physical.world.bytes r = s.flat.physical.world.bytes r ∧
    (post a).flat.physical.world.access r = s.flat.physical.world.access r ∧
    (geometry a).capacity r = g.capacity r ∧ (geometry a).byteAt r = g.byteAt r := by
  simp [post,world,geometry,old_region_ne wf a live]

theorem compatible {g layout s} (wf : WellFormed g layout s) (a : Supply g s) :
    (geometry a).Compatible (world a) := by
  intro r; by_cases eq : r = a.region
  · simp [world,geometry,eq]
  · simpa [world,geometry,eq] using wf.accounting.geometry r

theorem regions_disjoint {g layout s} (wf : WellFormed g layout s) (a : Supply g s) :
    RegionsDisjoint (world a) := by
  intro r rl q ql ne
  simp only [world,Finset.mem_insert] at rl ql
  rcases rl with rfl | rl <;> rcases ql with rfl | ql
  · exact False.elim (ne rfl)
  · simpa [world,old_region_ne wf a ql] using a.disjoint q ql
  · simpa [world,old_region_ne wf a rl] using (a.disjoint r rl).symm
  · simpa [world,old_region_ne wf a rl,old_region_ne wf a ql] using
      wf.accounting.regions r rl q ql ne

/-- Actual rich WF is derived from a PRE rich WF and raw resource input. No
post-WF, new Has, Allocation or Matched is a premise. Scope really extends. -/
theorem constructive_wellFormed {g layout s} (wf : WellFormed g layout s) (a : Supply g s) :
    WellFormed (geometry a) layout (post a) := by
  refine ⟨wf.toWellFormed,?_⟩
  have oldne : ∀ {id}, id ∈ s.ledger.active → (s.ledger.claim id).extent.region ≠ a.region :=
    fun active => old_claim_region_ne wf a active
  have clframe : ∀ {id}, id ∈ s.ledger.active → (ledger a).claim id = s.ledger.claim id :=
    fun active => old_claim_frame a active
  have oldfoot : ∀ id ∈ s.ledger.active,
      ((ledger a).claim id).extent.footprint (geometry a) =
        (s.ledger.claim id).extent.footprint g := by
    intro id active; rw [show (ledger a).claim id = _ from clframe active]
    exact footprint_frame a (oldne active)
  have freshfull : (ledger a).claim a.claim = .storage (extent a) := by simp [ledger]
  change Accounting (geometry a) layout (FlatLive s.flat.semantic)
    ⟨world a,s.flat.physical.placement⟩ (ledger a)
  constructor
  · constructor
    · exact compatible wf a
    · exact regions_disjoint wf a
    · intro r member
      simp only [ledger,Finset.mem_insert] at member
      rcases member with rfl | member
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (wf.accounting.scopeLive r member)
    · intro id active
      simp only [ledger,Finset.mem_insert] at active
      rcases active with rfl | active
      · simp [Claim.extent,extent,ledger]
      · rw [show (ledger a).claim id = _ from clframe active]
        exact Finset.mem_insert_of_mem (wf.accounting.inScope id active)
    · intro id active
      simp only [ledger,Finset.mem_insert] at active
      rcases active with rfl | active
      · simpa [freshfull,Claim.extent,extent] using a.positive
      · rw [show (ledger a).claim id = _ from clframe active]
        exact wf.accounting.positive id active
    · intro id active
      simp only [ledger,Finset.mem_insert] at active
      rcases active with rfl | active
      · simp [freshfull,Claim.extent,extent,Extent.Fits,Range.finish,geometry]
      · rw [show (ledger a).claim id = _ from clframe active]
        simpa [Extent.Fits,geometry,oldne active] using wf.accounting.fits id active
    · intro id active
      simp only [ledger,Finset.mem_insert] at active
      rcases active with rfl | active
      · simp [freshfull,Claim.Typed]
      · rw [show (ledger a).claim id = _ from clframe active]
        exact wf.accounting.typed id active
    · intro l
      rw [wf.accounting.roots l]
      constructor
      · rintro ⟨id,active,t,e,claim⟩
        exact ⟨id,Finset.mem_insert_of_mem active,t,e,(clframe active).trans claim⟩
      · rintro ⟨id,active,t,e,claim⟩
        simp only [ledger,Finset.mem_insert] at active
        rcases active with rfl | active
        · rw [freshfull] at claim; cases claim
        · exact ⟨id,active,t,e,(clframe active).symm.trans claim⟩
    · intro l pl
      rw [wf.accounting.placements l pl]
      constructor
      · rintro ⟨id,active,t,e,claim,placed⟩
        have ne : e.region ≠ a.region := by simpa [claim,Claim.extent] using oldne active
        refine ⟨id,Finset.mem_insert_of_mem active,t,e,(clframe active).trans claim,?_⟩
        simpa [Extent.placement,footprint_frame a ne] using placed
      · rintro ⟨id,active,t,e,claim,placed⟩
        simp only [ledger,Finset.mem_insert] at active
        rcases active with rfl | active
        · rw [freshfull] at claim; cases claim
        · have oldclaim := (clframe active).symm.trans claim
          have ne : e.region ≠ a.region := by simpa [oldclaim,Claim.extent] using oldne active
          exact ⟨id,active,t,e,oldclaim,by simpa [Extent.placement,footprint_frame a ne] using placed⟩
  · intro i ia j ja ne
    simp only [ledger,Finset.mem_insert] at ia ja
    rcases ia with rfl | ia <;> rcases ja with rfl | ja
    · exact False.elim (ne rfl)
    · rw [freshfull,Claim.extent,full_footprint,oldfoot j ja]
      exact Finset.disjoint_of_subset_right
        (fitting_extent_is_inside_backing wf.accounting.geometry (wf.accounting.fits j ja))
        (a.disjoint _ (surviving_claim_requires_live_backing wf.accounting ja))
    · rw [freshfull,Claim.extent,full_footprint,oldfoot i ia]
      exact (Finset.disjoint_of_subset_right
        (fitting_extent_is_inside_backing wf.accounting.geometry (wf.accounting.fits i ia))
        (a.disjoint _ (surviving_claim_requires_live_backing wf.accounting ia))).symm
    · rw [oldfoot i ia,oldfoot j ja]; exact wf.accounting.disjoint i ia j ja ne
  · have total : TotalFootprint (geometry a) (ledger a) =
        (Finset.range a.n).image a.byteAt ∪ TotalFootprint g s.ledger := by
      change (insert a.claim s.ledger.active).biUnion
        (fun id => ((ledger a).claim id).extent.footprint (geometry a)) = _
      rw [Finset.biUnion_insert,freshfull,Claim.extent,full_footprint]
      congr 1
      apply Finset.biUnion_congr rfl
      intro id active; exact oldfoot id active
    have expected : ExpectedFootprint (post a).flat.physical (ledger a) =
        (Finset.range a.n).image a.byteAt ∪ ExpectedFootprint s.flat.physical s.ledger := by
      simp only [ExpectedFootprint,post,ledger,Finset.biUnion_insert]
      simp only [world,ite_true]
      congr 1
      apply Finset.biUnion_congr rfl
      intro r member
      simp [old_region_ne wf a (wf.accounting.scopeLive r member)]
    exact total.trans (by rw [wf.accounting.coverage]; exact expected.symm)

theorem exact_fresh_byte_count {g s} (a : Supply g s) :
    ((Finset.range a.n).image a.byteAt).card = a.n := by
  rw [Finset.card_image_of_injective _ a.injective,Finset.card_range]

theorem exact_range_and_RW {g s} (a : Supply g s) :
    (extent a).range = ⟨0,(geometry a).capacity a.region⟩ ∧
    (world a).access a.region = ⟨true,true⟩ := by
  simp [extent,geometry,world]

theorem exactly_one_full_new_claim {g layout s} (wf : WellFormed g layout s) (a : Supply g s) :
    ∃! id, Has (post a).ledger id (.storage (extent a)) := by
  refine ⟨a.claim,full_has a,?_⟩
  intro other has
  by_contra ne
  apply nonempty_claim_cannot_be_covered_twice (constructive_wellFormed wf a).accounting
    has.1 (full_has a).1 ne
  rw [has.2,(full_has a).2]

end
end NewLang.Adjunct.OneBackingIssuerRich
