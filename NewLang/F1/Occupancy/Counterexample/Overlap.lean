import NewLang.F1.Occupancy.Counterexample.Claims

namespace NewLang.F1.Occupancy.Counterexample
open F0 Backing
noncomputable section

/-- Deliberately duplicate responsibility. This helper exists only in controls. -/
private def insertClaim (s : Ledger) (id : ClaimId) (c : Claim) : Ledger :=
  {s with active := insert id s.active,claim := fun i => if i = id then c else s.claim i}

private theorem inserted_shape {g layout live p s id c} (shape : AccountingShape g layout live p s)
    (fresh : id ∉ s.active) (region : c.extent.region ∈ s.scope)
    (positive : 0 < c.extent.range.length) (fits : c.extent.Fits g) (typed : c.Typed layout)
    (notRoot : ∀ t l e, c ≠ .root t l e) :
    AccountingShape g layout live p (insertClaim s id c) := by
  constructor
  · exact shape.geometry
  · exact shape.regions
  · exact shape.scopeLive
  · intro i active
    rcases Finset.mem_insert.mp active with rfl|pre
    · simpa [insertClaim] using region
    · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      simpa [insertClaim,different] using shape.inScope i pre
  · intro i active
    rcases Finset.mem_insert.mp active with rfl|pre
    · simpa [insertClaim] using positive
    · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      simpa [insertClaim,different] using shape.positive i pre
  · intro i active
    rcases Finset.mem_insert.mp active with rfl|pre
    · simpa [insertClaim] using fits
    · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      simpa [insertClaim,different] using shape.fits i pre
  · intro i active
    rcases Finset.mem_insert.mp active with rfl|pre
    · simpa [insertClaim] using typed
    · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      simpa [insertClaim,different] using shape.typed i pre
  · intro l; constructor
    · intro present
      rcases (shape.roots l).mp present with ⟨i,pre,t,e,eq⟩
      have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      exact ⟨i,Finset.mem_insert_of_mem pre,t,e,by simpa [insertClaim,different] using eq⟩
    · rintro ⟨i,active,t,e,eq⟩
      rcases Finset.mem_insert.mp active with rfl|pre
      · exact False.elim (notRoot t l e (by simpa [insertClaim] using eq))
      · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
        exact (shape.roots l).mpr ⟨i,pre,t,e,by simpa [insertClaim,different] using eq⟩
  · intro l pl; constructor
    · intro placed
      rcases (shape.placements l pl).mp placed with ⟨i,pre,t,e,eq,placed⟩
      have different : i ≠ id := fun eq => fresh (eq ▸ pre)
      exact ⟨i,Finset.mem_insert_of_mem pre,t,e,by simpa [insertClaim,different] using eq,placed⟩
    · rintro ⟨i,active,t,e,eq,placed⟩
      rcases Finset.mem_insert.mp active with rfl|pre
      · exact False.elim (notRoot t l e (by simpa [insertClaim] using eq))
      · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
        exact (shape.placements l pl).mpr ⟨i,pre,t,e,by simpa [insertClaim,different] using eq,placed⟩

private theorem inserted_coverage {g layout live p s id c} (wf : Accounting g layout live p s)
    (fresh : id ∉ s.active) (included : c.extent.footprint g ⊆ TotalFootprint g s) :
    TotalFootprint g (insertClaim s id c) = ExpectedFootprint p (insertClaim s id c) := by
  have total : TotalFootprint g (insertClaim s id c) = TotalFootprint g s := by
    ext byte; constructor
    · rintro member
      rcases Finset.mem_biUnion.mp member with ⟨i,active,im⟩
      rcases Finset.mem_insert.mp active with rfl|pre
      · exact included (by simpa [insertClaim] using im)
      · have different : i ≠ id := fun eq => fresh (eq ▸ pre)
        exact Finset.mem_biUnion.mpr ⟨i,pre,by simpa [insertClaim,different] using im⟩
    · rintro member
      rcases Finset.mem_biUnion.mp member with ⟨i,active,im⟩
      have different : i ≠ id := fun eq => fresh (eq ▸ active)
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_insert_of_mem active,by simpa [insertClaim,different] using im⟩
  rw [total,wf.coverage]; rfl

private theorem inserted_overlap {g s id c old byte} (fresh : id ∉ s.active)
    (active : old ∈ s.active) (inNew : byte ∈ c.extent.footprint g)
    (inOld : byte ∈ (s.claim old).extent.footprint g) : ¬ NoOverlap g (insertClaim s id c) := by
  intro wf
  have different : id ≠ old := fun eq => fresh (eq.symm ▸ active)
  have oldNotNew : old ≠ id := different.symm
  have disjoint := wf id (Finset.mem_insert_self _ _) old (Finset.mem_insert_of_mem active) different
  exact (Finset.disjoint_left.mp disjoint) (by simpa [insertClaim] using inNew)
    (by simpa [insertClaim,oldNotNew] using inOld)

private def duplicateRaw : Ledger := insertClaim slotLedger (cid 99) (.storage left)
private def duplicateSlot : Ledger := insertClaim liveLedger (cid 99) (.slot ty left)
private def duplicateFull (s : Ledger) : Ledger := insertClaim s (cid 99) (.storage full)

/-- All semantic/shape/coverage rules survive; only independent occupancy disjointness fails. -/
theorem storage_and_slot_overlap_isolated :
    F0.WellFormed (slotState rw).flat.semantic ∧
    AccountingShape geometry layout (FlatLive (slotState rw).flat.semantic) (slotState rw).flat.physical duplicateRaw ∧
    TotalFootprint geometry duplicateRaw = ExpectedFootprint (slotState rw).flat.physical duplicateRaw ∧
    ¬ NoOverlap geometry duplicateRaw := by
  have wf := (slot_state_wellFormed rw).accounting
  have fresh : cid 99 ∉ slotLedger.active := by
    simp [slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  refine ⟨(slot_state_wellFormed rw).toWellFormed,?_,?_,?_⟩
  · exact inserted_shape wf.toAccountingShape fresh (by change region 0 ∈ ({region 0} : Finset BackingRegionId); simp)
      (by decide) (by change 2 ≤ 4; decide) trivial (by intros; simp)
  · apply inserted_coverage wf fresh
    intro byte member
    exact Finset.mem_biUnion.mpr ⟨cid 3,by simp [slotState,slotLedger,consumeOne],by simpa [slotState,slotLedger,consumeOne,Claim.extent] using member⟩
  · apply inserted_overlap (byte := (⟨0⟩ : AbstractByteId)) fresh (old := cid 3)
    · simp [slotLedger,consumeOne]
    · decide
    · change (⟨0⟩ : AbstractByteId) ∈ left.footprint geometry; decide

theorem slot_and_live_root_overlap_isolated :
    F0.WellFormed (first rw).flat.semantic ∧
    AccountingShape geometry layout (FlatLive (first rw).flat.semantic) (first rw).flat.physical duplicateSlot ∧
    TotalFootprint geometry duplicateSlot = ExpectedFootprint (first rw).flat.physical duplicateSlot ∧
    ¬ NoOverlap geometry duplicateSlot := by
  have wf := (first_wellFormed rw).accounting
  have fresh : cid 99 ∉ liveLedger.active := by
    simp [liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  refine ⟨(first_wellFormed rw).toWellFormed,?_,?_,?_⟩
  · exact inserted_shape wf.toAccountingShape fresh (by change region 0 ∈ ({region 0} : Finset BackingRegionId); simp)
      (by decide) (by change 2 ≤ 4; decide) rfl (by intros; simp)
  · apply inserted_coverage wf fresh
    intro byte member
    exact Finset.mem_biUnion.mpr ⟨cid 4,by simp [first,liveLedger,consumeOne],by simpa [first,liveLedger,consumeOne,Claim.extent] using member⟩
  · apply inserted_overlap (byte := (⟨0⟩ : AbstractByteId)) fresh (old := cid 4)
    · simp [liveLedger,consumeOne]
    · decide
    · change (⟨0⟩ : AbstractByteId) ∈ left.footprint geometry; decide

private theorem full_reconstruction_control (s : State) (wf : WellFormed geometry layout s)
    (scope : s.ledger.scope = {region 0}) (bytes : ExpectedFootprint s.flat.physical s.ledger = full.footprint geometry)
    (fresh : cid 99 ∉ s.ledger.active) (old : ClaimId) (oldActive : old ∈ s.ledger.active)
    (oldExtent : (s.ledger.claim old).extent = left) :
    AccountingShape geometry layout (FlatLive s.flat.semantic) s.flat.physical (duplicateFull s.ledger) ∧
    TotalFootprint geometry (duplicateFull s.ledger) = ExpectedFootprint s.flat.physical (duplicateFull s.ledger) ∧
    ¬ NoOverlap geometry (duplicateFull s.ledger) := by
  refine ⟨inserted_shape wf.accounting.toAccountingShape fresh (by rw [scope]; exact Finset.mem_singleton_self _)
    (by decide) (by change 4 ≤ 4; decide) trivial (by intros; simp),?_,?_⟩
  · apply inserted_coverage wf.accounting fresh
    rw [wf.accounting.coverage,bytes]; exact Finset.Subset.refl _
  · apply inserted_overlap (byte := (⟨0⟩ : AbstractByteId)) fresh oldActive
    · decide
    · rw [oldExtent]; decide

/-- Reconstructing full Storage while either a slot or live root is outstanding
keeps coverage and every shape rule, and duplicates existing responsibility. -/
theorem outstanding_slot_blocks_full_storage :
    AccountingShape geometry layout (FlatLive (slotState rw).flat.semantic) (slotState rw).flat.physical (duplicateFull slotLedger) ∧
    TotalFootprint geometry (duplicateFull slotLedger) = ExpectedFootprint (slotState rw).flat.physical (duplicateFull slotLedger) ∧
    ¬ NoOverlap geometry (duplicateFull slotLedger) := by
  apply full_reconstruction_control (slotState rw) (slot_state_wellFormed rw) rfl
    (by simp [ExpectedFootprint,slotState,slotLedger,splitLedger,splitCandidate,rawLedger,consumeOne,flat,physical,world,full,Extent.footprint,Range.positions,Range.finish])
    (old := cid 3)
  · simp [slotState,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · simp [slotState,slotLedger,consumeOne]
  · rfl

theorem outstanding_root_blocks_full_storage :
    AccountingShape geometry layout (FlatLive (first rw).flat.semantic) (first rw).flat.physical (duplicateFull liveLedger) ∧
    TotalFootprint geometry (duplicateFull liveLedger) = ExpectedFootprint (first rw).flat.physical (duplicateFull liveLedger) ∧
    ¬ NoOverlap geometry (duplicateFull liveLedger) := by
  apply full_reconstruction_control (first rw) (first_wellFormed rw) rfl
    (by simp [ExpectedFootprint,first,liveLedger,slotLedger,splitLedger,splitCandidate,rawLedger,consumeOne,flat,physical,world,full,Extent.footprint,Range.positions,Range.finish])
    (old := cid 4)
  · simp [first,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · simp [first,liveLedger,consumeOne]
  · rfl

end
end NewLang.F1.Occupancy.Counterexample
