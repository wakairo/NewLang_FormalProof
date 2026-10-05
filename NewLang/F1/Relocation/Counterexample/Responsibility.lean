import NewLang.F1.Relocation.Counterexample.Controls

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing Occupancy
open Occupancy.Counterexample (geometry layout ty cid region rw)
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


private def overlapPost := after .overlap rw ∅ ∅
def duplicateIntersection : Ledger := insertClaim overlapPost.accounted.ledger (cid 8) (.storage ⟨region 0,⟨1,1⟩⟩)
def unconsumedDestinationRaw : Ledger := insertClaim overlapPost.accounted.ledger (cid 1) (.storage (inputExtent .overlap))

/-- All semantic and accounting shape/coverage obligations survive. Only the
unique-responsibility condition is broken, at the overlapping byte 1. -/
theorem overlap_intersection_raw_duplication_rejected :
    AccountingShape geometry layout (fun l => l ∈ overlapPost.accounted.base.semantic.liveRoots)
      overlapPost.accounted.base.physical duplicateIntersection ∧
    TotalFootprint geometry duplicateIntersection = ExpectedFootprint overlapPost.accounted.base.physical duplicateIntersection ∧
    ¬ NoOverlap geometry duplicateIntersection := by
  have wf := (independent_after_wellFormed .overlap rw).accounting
  refine ⟨inserted_shape wf.toAccountingShape (by decide) (by simp [overlapPost,after,candidate,ledgerCandidate,before,beforeLedger,regions,Claim.extent])
    (by decide) (by change 2 ≤ 4; decide) trivial (by intro t l e; simp),
    inserted_coverage wf (by decide) (by decide),?_⟩
  exact inserted_overlap (old := cid 4) (byte := ⟨1⟩) (by decide) (by decide) (by decide) (by decide)

/-- D-S is still covered as part of the new root; retaining its independent raw
carrier duplicates responsibility, despite exact union coverage and valid shape. -/
theorem destination_raw_not_consumed_rejected :
    AccountingShape geometry layout (fun l => l ∈ overlapPost.accounted.base.semantic.liveRoots)
      overlapPost.accounted.base.physical unconsumedDestinationRaw ∧
    TotalFootprint geometry unconsumedDestinationRaw = ExpectedFootprint overlapPost.accounted.base.physical unconsumedDestinationRaw ∧
    ¬ NoOverlap geometry unconsumedDestinationRaw := by
  have wf := (independent_after_wellFormed .overlap rw).accounting
  refine ⟨inserted_shape wf.toAccountingShape (by decide) (by simp [overlapPost,after,candidate,ledgerCandidate,before,beforeLedger,regions,inputExtent,Claim.extent])
    (by decide) (by change 3 ≤ 4; decide) trivial (by intro t l e; simp),
    inserted_coverage wf (by decide) (by decide),?_⟩
  exact inserted_overlap (old := cid 4) (byte := ⟨2⟩) (by decide) (by decide) (by decide) (by decide)

private def removeRaw (s : Ledger) (id : ClaimId) : Ledger := {s with active := s.active.erase id}
private theorem removed_shape {g layout live p s id e} (shape : AccountingShape g layout live p s)
    (raw : s.claim id = .storage e) : AccountingShape g layout live p (removeRaw s id) := by
  constructor
  · exact shape.geometry
  · exact shape.regions
  · exact shape.scopeLive
  · intro i active; exact shape.inScope i (Finset.mem_of_mem_erase active)
  · intro i active; exact shape.positive i (Finset.mem_of_mem_erase active)
  · intro i active; exact shape.fits i (Finset.mem_of_mem_erase active)
  · intro i active; exact shape.typed i (Finset.mem_of_mem_erase active)
  · intro l; constructor
    · intro live
      rcases (shape.roots l).mp live with ⟨i,active,t,q,eq⟩
      have different : i ≠ id := by intro same; subst i; rw [raw] at eq; cases eq
      exact ⟨i,Finset.mem_erase.mpr ⟨different,active⟩,t,q,eq⟩
    · rintro ⟨i,active,t,q,eq⟩; exact (shape.roots l).mpr ⟨i,Finset.mem_of_mem_erase active,t,q,eq⟩
  · intro l pl; constructor
    · intro placed
      rcases (shape.placements l pl).mp placed with ⟨i,active,t,q,eq,place⟩
      have different : i ≠ id := by intro same; subst i; rw [raw] at eq; cases eq
      exact ⟨i,Finset.mem_erase.mpr ⟨different,active⟩,t,q,eq,place⟩
    · rintro ⟨i,active,t,q,eq,place⟩; exact (shape.placements l pl).mpr ⟨i,Finset.mem_of_mem_erase active,t,q,eq,place⟩

def lostSourceRaw : Ledger := removeRaw overlapPost.accounted.ledger (cid 3)

/-- All root placement, shape and no-overlap rules hold; S-D byte 0 is missing.
This isolates exact coverage, rather than weakening the live-root invariant. -/
theorem source_difference_responsibility_lost_rejected :
    AccountingShape geometry layout (fun l => l ∈ overlapPost.accounted.base.semantic.liveRoots)
      overlapPost.accounted.base.physical lostSourceRaw ∧
    NoOverlap geometry lostSourceRaw ∧
    (⟨0⟩ : AbstractByteId) ∈ ExpectedFootprint overlapPost.accounted.base.physical lostSourceRaw ∧
    (⟨0⟩ : AbstractByteId) ∉ TotalFootprint geometry lostSourceRaw := by
  have wf := (independent_after_wellFormed .overlap rw).accounting
  refine ⟨removed_shape wf.toAccountingShape (e := outputExtent .overlap) (by decide),?_,by decide,by decide⟩
  intro i ia j ja neq
  exact wf.disjoint i (Finset.mem_of_mem_erase ia) j (Finset.mem_of_mem_erase ja) neq

end
end NewLang.F1.Relocation.Counterexample
