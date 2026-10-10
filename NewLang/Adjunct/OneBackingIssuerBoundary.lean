import NewLang.Adjunct.SourceRichBoundary

/-! Issue #51: the FIRST issuer boundary, not an allocator semantics extension.
No source Allocation interpreter, issuer contract, or grant rule is stipulated.
All relations below are the existing accepted rich constructors/accounting.
The concrete ledger is an accepted raw-split control, NOT a OneBacking result. -/
namespace NewLang.Adjunct.OneBackingIssuerBoundary
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Even a full raw claim in accepted accounting refers to an ALREADY LIVE R.
It does not express the source event which issued R or the separate Allocation. -/
theorem storage_requires_existing_backing
    {g : Geometry} {layout : Layout} {live : RootLocationId → Prop}
    {physical : PhysicalState} {ledger : Ledger} {id : ClaimId} {e : Extent}
    (wf : Accounting g layout live physical ledger)
    (raw : Has ledger id (.storage e)) : e.region ∈ physical.world.liveRegions := by
  simpa only [raw.2,Claim.extent] using surviving_claim_requires_live_backing wf raw.1

/-- Raw→slot cannot be substituted for the missing allocator-success step. -/
theorem into_slot_requires_existing_backing
    {g : Geometry} {layout : Layout} {aligned : Prop}
    {live : RootLocationId → Prop} {physical : PhysicalState}
    {ledger post : Ledger} {source result : ClaimId} {t : TypeId} {e : Extent}
    (wf : Accounting g layout live physical ledger)
    (convert : RawIntoSlot layout aligned ledger source result t e post) :
    e.region ∈ physical.world.liveRegions :=
  storage_requires_existing_backing wf convert.sourceClaim

/-- Actual initialization requires preexisting live backing independently of
any post-WF or full-range premise. This is a constructor requirement, not a
claim that canonical source allocation is impossible. -/
theorem initialize_requires_existing_backing
    {g : Geometry} {sites : RootSiteLayout} {ci tc : Prop}
    {s post : F1.Occupancy.State} {source result : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {pkg : PackageId} {d : DomainId}
    {inc : IncarnationId} {vf : ValueFactId} {access : Evidence}
    (start : F1.Occupancy.RawInitialize g sites ci tc s source result t e
      l pkg d inc vf access post) : e.region ∈ s.flat.physical.world.liveRegions := by
  have same : e.region = access.region := start.backing.region
  rw [same]
  exact start.backing.evidence.1

/-- A fresh region (absent from the PRE-world) cannot be issued by this rich
constructor. Source allocation needs its own introduction/refinement boundary. -/
theorem initialize_is_not_fresh_region_issuance
    {g : Geometry} {sites : RootSiteLayout} {ci tc : Prop}
    {s post : F1.Occupancy.State} {source result : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {pkg : PackageId} {d : DomainId}
    {inc : IncarnationId} {vf : ValueFactId} {access : Evidence}
    (fresh : e.region ∉ s.flat.physical.world.liveRegions) :
    ¬ F1.Occupancy.RawInitialize g sites ci tc s source result t e
      l pkg d inc vf access post := fun start => fresh (initialize_requires_existing_backing start)

/-- Both accepted empty-claim conversions preserve the fixed accounting scope.
They consume/produce existing byte responsibility; they do not add issuer scope. -/
theorem conversions_do_not_introduce_region_scope
    {layout : Layout} {aligned : Prop} {raw slot erased : Ledger}
    {source middle result : ClaimId} {t : TypeId} {e : Extent}
    (convert : RawIntoSlot layout aligned raw source middle t e slot)
    (erase : RawEraseSlot slot middle result t e erased) :
    slot.scope = raw.scope ∧ erased.scope = raw.scope := by
  have scope : slot.scope = raw.scope := by rw [convert.post_eq]; rfl
  exact ⟨scope,by rw [erase.post_eq]; exact scope⟩

/-- Concrete accepted control: split the accepted four-byte full raw into a
three-byte prefix and an independently owned LAST BYTE. No Allocation exists
in this representation, and no source OneBacking issuance is claimed. -/
def lastByteLedger : Ledger :=
  splitCandidate Counterexample.rawLedger (Counterexample.cid 0)
    (Counterexample.cid 1) (Counterexample.cid 20) Counterexample.full 3

theorem last_byte_split_raw :
    RawSplit Counterexample.rawLedger (Counterexample.cid 0)
      (Counterexample.cid 1) (Counterexample.cid 20) Counterexample.full 3 lastByteLedger :=
  ⟨⟨by simp [Counterexample.rawLedger],rfl⟩,by decide,by decide,
    by simp [Counterexample.rawLedger,Counterexample.cid],
    by simp [Counterexample.rawLedger,Counterexample.cid],by decide,rfl⟩

theorem last_byte_accounting :
    Accounting Counterexample.geometry Counterexample.layout
      (FlatLive Counterexample.rawState.flat.semantic)
      Counterexample.rawState.flat.physical lastByteLedger := by
  have old := Counterexample.raw_state_wellFormed.accounting
  have cases : ∀ id ∈ lastByteLedger.active,
      id = Counterexample.cid 1 ∨ id = Counterexample.cid 20 := by
    intro id active
    simpa [lastByteLedger,splitCandidate,Counterexample.rawLedger] using active
  have noRoot : ∀ id ∈ lastByteLedger.active, ∀ t l e,
      lastByteLedger.claim id ≠ .root t l e := by
    intro id active t l e
    rcases cases id active with rfl | rfl <;>
      simp [lastByteLedger,splitCandidate,Counterexample.cid]
  constructor
  · constructor
    · exact old.geometry
    · exact old.regions
    · exact old.scopeLive
    · intro id active
      rcases cases id active with rfl | rfl <;>
        simp [lastByteLedger,splitCandidate,Counterexample.rawLedger,
          Counterexample.cid,Counterexample.full,Extent.left,Extent.right,Claim.extent]
    · intro id active
      rcases cases id active with rfl | rfl <;>
        simp [lastByteLedger,splitCandidate,Counterexample.cid,Counterexample.full,
          Extent.left,Extent.right,Range.left,Range.right,Claim.extent]
    · intro id active
      rcases cases id active with rfl | rfl <;>
        simp [lastByteLedger,splitCandidate,Counterexample.cid,Counterexample.full,
          Extent.left,Extent.right,Range.left,Range.right,Claim.extent,
          Extent.Fits,Range.finish,Counterexample.geometry]
    · intro id active
      rcases cases id active with rfl | rfl <;>
        simp [lastByteLedger,splitCandidate,Counterexample.cid,Claim.Typed]
    · intro l
      constructor
      · intro live
        rcases (old.roots l).mp live with ⟨id,active,t,e,claim⟩
        simp [Counterexample.rawState,Counterexample.rawLedger] at active claim
      · rintro ⟨id,active,t,e,claim⟩
        exact False.elim (noRoot id active t l e claim)
    · intro l pl
      constructor
      · intro placed
        simp [Counterexample.rawState,Counterexample.flat,Counterexample.physical] at placed
      · rintro ⟨id,active,t,e,claim,_⟩
        exact False.elim (noRoot id active t l e claim)
  · intro a aa b ba different
    rcases cases a aa with rfl | rfl <;> rcases cases b ba with rfl | rfl
    · exact False.elim (different rfl)
    · simpa [lastByteLedger,splitCandidate,Counterexample.cid,Claim.extent] using
        split_extents_disjoint Counterexample.geometry Counterexample.full 3
    · simpa [lastByteLedger,splitCandidate,Counterexample.cid,Claim.extent] using
        (split_extents_disjoint Counterexample.geometry Counterexample.full 3).symm
    · exact False.elim (different rfl)
  · rw [split_conserves_all_byte_responsibility Counterexample.geometry last_byte_split_raw]
    exact old.coverage

theorem last_byte_split_is_rich_wellFormed :
    WellFormed Counterexample.geometry Counterexample.layout
      ⟨Counterexample.rawState.flat,lastByteLedger⟩ :=
  ⟨Counterexample.raw_state_wellFormed.toWellFormed,last_byte_accounting⟩

theorem complete_accounting_does_not_make_each_storage_full :
    Has lastByteLedger (Counterexample.cid 1) (.storage (Counterexample.full.left 3)) ∧
    Has lastByteLedger (Counterexample.cid 20) (.storage (Counterexample.full.right 3)) ∧
    TotalFootprint Counterexample.geometry lastByteLedger =
      TotalFootprint Counterexample.geometry Counterexample.rawLedger ∧
    (Counterexample.full.left 3).range ≠
      ⟨0,Counterexample.geometry.capacity Counterexample.full.region⟩ ∧
    (Counterexample.full.right 3).range.length = 1 :=
  ⟨(split_consumes_source_and_produces_two last_byte_split_raw).2.1,
    (split_consumes_source_and_produces_two last_byte_split_raw).2.2,
    split_conserves_all_byte_responsibility _ last_byte_split_raw,by decide,rfl⟩

def lostLastByte : Ledger :=
  {lastByteLedger with active := {Counterexample.cid 1}}

/-- Loss of the final byte is actually rejected by accepted coverage. That law
is about byte claims, not about loss of the separate opaque Allocation value. -/
theorem losing_last_byte_breaks_accounting :
    ¬ Accounting Counterexample.geometry Counterexample.layout
      (FlatLive Counterexample.rawState.flat.semantic)
      Counterexample.rawState.flat.physical lostLastByte := by
  intro wf
  have absent : Counterexample.geometry.byteAt (Counterexample.region 0) 3 ∉
      TotalFootprint Counterexample.geometry lostLastByte := by
    simp [TotalFootprint,lostLastByte,lastByteLedger,splitCandidate,
      Counterexample.rawLedger,Counterexample.cid,Counterexample.full,Claim.extent,
      Extent.left,Range.left,Extent.footprint,Range.positions,Range.finish,
      Counterexample.geometry,Counterexample.region]
  have present : Counterexample.geometry.byteAt (Counterexample.region 0) 3 ∈
      ExpectedFootprint Counterexample.rawState.flat.physical lostLastByte := by
    simp [ExpectedFootprint,lostLastByte,lastByteLedger,splitCandidate,
      Counterexample.rawLedger,Counterexample.rawState,Counterexample.flat,
      Counterexample.physical,Counterexample.world,Counterexample.geometry,Counterexample.region]
  exact absent (wf.coverage.symm ▸ present)

end
end NewLang.Adjunct.OneBackingIssuerBoundary
