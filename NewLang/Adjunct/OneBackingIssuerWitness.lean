import NewLang.Adjunct.OneBackingIssuerSource

namespace NewLang.Adjunct.OneBackingIssuerWitness
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource
noncomputable section

/-- A nonempty accepted-rich raw frame, with no typed authority hidden in F0. -/
def oneRaw (g : Geometry) (r : BackingRegionId) : F1.Occupancy.State where
  flat := ⟨F0.State.empty,⟨⟨{r},fun q => (Finset.range (g.capacity q)).image (g.byteAt q),
    fun _ => ⟨true,true⟩⟩,fun _ => none⟩⟩
  ledger := ⟨{r},{⟨0⟩},fun _ => .storage ⟨r,⟨0,g.capacity r⟩⟩⟩

theorem one_raw_wellFormed (g : Geometry) (layout : Layout) (r : BackingRegionId)
    (positive : 0 < g.capacity r) : WellFormed g layout (oneRaw g r) := by
  refine ⟨F0.empty_wellFormed,?_⟩
  constructor
  · constructor
    · intro q; rfl
    · intro a aa b ba ne
      simp only [oneRaw,Finset.mem_singleton] at aa ba
      exact False.elim (ne (aa.trans ba.symm))
    · intro q member; exact member
    · intro id _; exact Finset.mem_singleton_self _
    · intro id _; exact positive
    · intro id _; simp [oneRaw,Claim.extent,Extent.Fits,Range.finish]
    · intro id _; trivial
    · intro l
      simp [oneRaw,FlatLive,F0.State.empty]
    · intro l pl
      simp [oneRaw]
  · intro a aa b ba ne
    simp only [oneRaw,Finset.mem_singleton] at aa ba
    exact False.elim (ne (aa.trans ba.symm))
  · simp [TotalFootprint,ExpectedFootprint,oneRaw,Claim.extent,Extent.footprint,
      Range.positions,Range.finish]

/-- Illustrative positive target layout; this is NOT a claim about C's sizeof.
The simulation above is parameterized over the chosen Node layout obligation. -/
def target : Target := ⟨.node,24,by decide,8,by decide⟩
def ok : Success target := ⟨4096,by decide⟩
def oldGrant : Grant := ⟨40,40,1000,24,2048⟩
def beforeSource : Source := ⟨41,1004,{oldGrant},oldGrant.edges,{1000,1001,1002},∅⟩
def beforeGeometry : Geometry where
  capacity r := if r = ⟨0⟩ then 24 else 0
  byteAt r n := ⟨r.index*200+n⟩
  injective r := by intro a b eq; have := congrArg AbstractByteId.index eq; simp at this; omega

def beforeRich := oneRaw beforeGeometry ⟨0⟩
def layout : Layout := ⟨fun _ => 24,by intro _; decide⟩

def beforeInterpretation : Interpretation where
  region r := ⟨if r = 40 then 0 else r+200⟩
  allocation v := if v = 1000 then some ⟨0⟩ else none
  rawClaim _ := ⟨0⟩
  usedRegions := (Finset.range 41).image (fun r => ⟨if r = 40 then 0 else r+200⟩)

theorem before_source_wellFormed : SourceWF beforeSource := by
  constructor
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p; decide
  · intro p pm q qm _
    simp only [beforeSource,Finset.mem_singleton] at pm qm
    exact pm.trans qm.symm
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p; decide
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p; rfl
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p; decide
  · simp [beforeSource]
  · exact edges_unique oldGrant
  · rfl

theorem before_rich_wellFormed : WellFormed beforeGeometry layout beforeRich :=
  one_raw_wellFormed _ _ _ (by decide)

theorem before_refines : Refines beforeSource beforeGeometry beforeRich beforeInterpretation := by
  constructor
  · intro r below
    exact Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr below,rfl⟩
  · intro r _ q _ eq
    have eq := congrArg BackingRegionId.index eq
    simp only [beforeInterpretation] at eq
    by_cases re : r = 40 <;> by_cases qe : q = 40 <;> simp [re,qe] at eq <;> omega
  · intro v
    simp [beforeInterpretation,beforeSource,oldGrant,eq_comm]
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p
    simp [beforeInterpretation,oldGrant]
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p
    simp [Has,beforeRich,oneRaw,beforeGeometry,beforeInterpretation,oldGrant]
  · intro p member; simp only [beforeSource,Finset.mem_singleton] at member; subst p
    simp [beforeGeometry,beforeInterpretation,oldGrant]
  · simp [beforeRich,oneRaw,beforeSource,beforeInterpretation,oldGrant]
  · simp [beforeRich,oneRaw,beforeSource,beforeInterpretation,oldGrant]
  · simp [beforeRich,oneRaw,beforeSource,beforeInterpretation]
  · rfl
  · rfl
  · simp [beforeSource]

/-- R_B=7 is distinct from source lineage serial 41 and numeric address 4096. -/
def supply : OneBackingIssuerRich.Supply beforeGeometry beforeRich where
  region := ⟨7⟩
  claim := ⟨9⟩
  n := 24
  positive := by decide
  byteAt n := ⟨100+n⟩
  injective := by intro a b eq; have := congrArg AbstractByteId.index eq; simp at this; omega
  freshRegion := by simp [beforeRich,oneRaw]
  freshClaim := by simp [beforeRich,oneRaw]
  disjoint r live := by
    simp only [beforeRich,oneRaw,Finset.mem_singleton] at live
    subst r
    apply Finset.disjoint_left.mpr
    intro byte new old
    rcases Finset.mem_image.mp new with ⟨i,ib,ie⟩
    rcases Finset.mem_image.mp old with ⟨j,jb,je⟩
    have eq := congrArg AbstractByteId.index (ie.trans je.symm)
    simp only [beforeGeometry] at eq
    have jb := Finset.mem_range.mp jb
    simp only [beforeGeometry,ite_true] at jb
    omega

theorem supply_history_fresh : supply.region ∉ beforeInterpretation.usedRegions := by
  intro mem
  rcases Finset.mem_image.mp mem with ⟨r,_,eq⟩
  have eq := congrArg BackingRegionId.index eq
  simp only [supply] at eq
  split at eq <;> omega

def afterSource := somePost target beforeSource ok
def afterRich := OneBackingIssuerRich.post supply
def afterGeometry := OneBackingIssuerRich.geometry supply
def afterInterpretation := interpretationPost supply beforeSource beforeInterpretation

theorem concrete_some_simulation :
    Step target beforeSource (.some 1007) afterSource ∧ SourceWF afterSource ∧
    Refines afterSource afterGeometry afterRich afterInterpretation ∧
    WellFormed afterGeometry layout afterRich :=
  some_simulation before_source_wellFormed (by simp [beforeSource]) before_rich_wellFormed
    before_refines ok supply rfl supply_history_fresh

theorem concrete_none_simulation :
    Step target beforeSource .none beforeSource ∧ SourceWF beforeSource ∧
    Refines beforeSource beforeGeometry beforeRich beforeInterpretation ∧
    WellFormed beforeGeometry layout beforeRich :=
  none_simulation before_source_wellFormed (by simp [beforeSource]) before_rich_wellFormed before_refines

theorem concrete_nonempty_frame :
    beforeRich.flat.physical.world.liveRegions = {⟨0⟩} ∧
    afterRich.flat.physical.world.liveRegions = {⟨7⟩,⟨0⟩} ∧
    afterRich.ledger.scope = {⟨7⟩,⟨0⟩} ∧
    afterRich.ledger.active = {⟨9⟩,⟨0⟩} ∧
    afterRich.flat.physical.world.bytes ⟨0⟩ = beforeRich.flat.physical.world.bytes ⟨0⟩ ∧
    afterInterpretation.allocation 1000 = some ⟨0⟩ ∧
    afterInterpretation.allocation 1004 = some ⟨7⟩ ∧
    afterInterpretation.region oldGrant.region ≠
      afterInterpretation.region (freshGrant target beforeSource ok).region := by
  simp [beforeRich,oneRaw,afterRich,OneBackingIssuerRich.post,OneBackingIssuerRich.world,
    OneBackingIssuerRich.ledger,supply,afterInterpretation,interpretationPost,
    beforeInterpretation,beforeSource,oldGrant,freshGrant,ok]

/-- Address observation of a RETIRED lineage entry, with no surviving A/raw.
This avoids suggesting that live same-address overlapping allocations are safe. -/
def retiredObservation : Nat × Nat := (0,4096)

theorem recycled_address_does_not_recycle_semantic_R :
    retiredObservation.1 < beforeSource.nextRegion ∧
    beforeInterpretation.region retiredObservation.1 = ⟨200⟩ ∧
    beforeInterpretation.region retiredObservation.1 ∉ beforeRich.flat.physical.world.liveRegions ∧
    retiredObservation.2 = (freshGrant target beforeSource ok).observedAddress ∧
    afterInterpretation.region retiredObservation.1 ≠
      afterInterpretation.region (freshGrant target beforeSource ok).region := by
  simp [retiredObservation,beforeInterpretation,beforeSource,beforeRich,oneRaw,
    freshGrant,ok,afterInterpretation,interpretationPost,supply]

end
end NewLang.Adjunct.OneBackingIssuerWitness
