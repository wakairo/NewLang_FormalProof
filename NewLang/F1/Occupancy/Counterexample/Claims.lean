import NewLang.F1.Occupancy.Counterexample.Cycle

namespace NewLang.F1.Occupancy.Counterexample
open F0 Backing
noncomputable section

private def twoRaw (a b : Extent) : Ledger :=
  ⟨{region 0},{cid 1,cid 20},fun id => if id = cid 1 then .storage a else .storage b⟩

private theorem raw_shape (s : Ledger) (scope : s.scope = {region 0})
    (claims : ∀ id ∈ s.active, ∃ e, s.claim id = .storage e ∧ e.region = region 0 ∧
      0 < e.range.length ∧ e.Fits geometry) :
    AccountingShape geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical s := by
  constructor
  · intro r; rfl
  · exact raw_state_wellFormed.accounting.regions
  · intro r member; simpa [scope,rawState,flat,physical,world] using member
  · intro id active; rcases claims id active with ⟨e,eq,re,_,_⟩; rw [eq,scope]; exact Finset.mem_singleton.mpr re
  · intro id active; rcases claims id active with ⟨e,eq,_,positive,_⟩; rw [eq]; exact positive
  · intro id active; rcases claims id active with ⟨e,eq,_,_,fits⟩; rw [eq]; exact fits
  · intro id active; rcases claims id active with ⟨e,eq,_⟩; rw [eq]; trivial
  · intro l; constructor
    · rintro ⟨r,h⟩; simp [rawState,flat,semantic] at h
    · rintro ⟨id,active,t,e,eq⟩; rcases claims id active with ⟨q,claim,_⟩; rw [claim] at eq; cases eq
  · intro l pl; constructor
    · intro h; simp [rawState,flat,physical] at h
    · rintro ⟨id,active,t,e,eq,_⟩; rcases claims id active with ⟨q,claim,_⟩; rw [claim] at eq; cases eq

private theorem two_raw_shape {a b : Extent} (ar : a.region = region 0) (br : b.region = region 0)
    (ap : 0 < a.range.length) (bp : 0 < b.range.length) (af : a.Fits geometry) (bf : b.Fits geometry) :
    AccountingShape geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical (twoRaw a b) := by
  apply raw_shape _ rfl
  intro id active
  have cases : id = cid 1 ∨ id = cid 20 := by simpa [twoRaw] using active
  rcases cases with rfl|rfl
  · exact ⟨a,by simp [twoRaw],ar,ap,af⟩
  · exact ⟨b,by simp [twoRaw,cid],br,bp,bf⟩

private def gapLeft : Extent := ⟨region 0,⟨0,1⟩⟩
private def overlapLeft : Extent := ⟨region 0,⟨0,3⟩⟩
private def gapLedger : Ledger := twoRaw gapLeft right
private def overlapLedger : Ledger := twoRaw overlapLeft right

/-- Source is valid; endpoint candidates conserve union but introduce an empty result. -/
theorem endpoint_split_controls :
    WellFormed geometry layout rawState ∧
    (full.left 0).range.length = 0 ∧ (full.right 4).range.length = 0 ∧
    ¬ RawSplit rawLedger (cid 0) (cid 1) (cid 20) full 0
      (splitCandidate rawLedger (cid 0) (cid 1) (cid 20) full 0) ∧
    ¬ RawSplit rawLedger (cid 0) (cid 1) (cid 20) full 4
      (splitCandidate rawLedger (cid 0) (cid 1) (cid 20) full 4) :=
  ⟨raw_state_wellFormed,rfl,rfl,split_rejects_left_endpoint,split_rejects_right_endpoint⟩

/-- Shape and disjointness hold; only exact coverage fails, at byte 1. -/
theorem gap_split_isolates_lost_responsibility :
    AccountingShape geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical gapLedger ∧
    NoOverlap geometry gapLedger ∧
    (⟨1⟩ : AbstractByteId) ∈ ExpectedFootprint rawState.flat.physical gapLedger ∧
    (⟨1⟩ : AbstractByteId) ∉ TotalFootprint geometry gapLedger := by
  refine ⟨two_raw_shape rfl rfl (by decide) (by decide) (by change 1 ≤ 4; decide) (by change 4 ≤ 4; decide),?_,?_,?_⟩
  · intro i ia j ja neq
    have ic : i = cid 1 ∨ i = cid 20 := by simpa [gapLedger,twoRaw] using ia
    have jc : j = cid 1 ∨ j = cid 20 := by simpa [gapLedger,twoRaw] using ja
    rcases ic with rfl|rfl <;> rcases jc with rfl|rfl
    · exact False.elim (neq rfl)
    · change Disjoint (gapLeft.footprint geometry) (right.footprint geometry); decide
    · change Disjoint (right.footprint geometry) (gapLeft.footprint geometry); decide
    · exact False.elim (neq rfl)
  · change (⟨1⟩ : AbstractByteId) ∈ (world rw).bytes (region 0); decide
  · change (⟨1⟩ : AbstractByteId) ∉ (gapLeft.footprint geometry ∪ right.footprint geometry); decide

/-- Exact coverage and all shape rules hold; only no-overlap fails, at byte 2. -/
theorem overlapping_split_isolates_duplication :
    AccountingShape geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical overlapLedger ∧
    TotalFootprint geometry overlapLedger = ExpectedFootprint rawState.flat.physical overlapLedger ∧
    ¬ NoOverlap geometry overlapLedger := by
  refine ⟨two_raw_shape rfl rfl (by decide) (by decide) (by change 3 ≤ 4; decide) (by change 4 ≤ 4; decide),?_,?_⟩
  · change overlapLeft.footprint geometry ∪ right.footprint geometry = (world rw).bytes (region 0); decide
  · intro valid
    have disjoint := valid (cid 1) (by simp [overlapLedger,twoRaw]) (cid 20) (by simp [overlapLedger,twoRaw]) (by decide)
    exact (Finset.disjoint_left.mp disjoint) (show (⟨2⟩ : AbstractByteId) ∈ _ from by decide)
      (show (⟨2⟩ : AbstractByteId) ∈ _ from by decide)

/-- A correct full accounting with an explicit raw carrier filling the gap. -/
private def gapSource : Ledger :=
  ⟨{region 0},{cid 0,cid 1,cid 2},fun id => if id = cid 0 then .storage gapLeft
    else if id = cid 1 then .storage right else .storage ⟨region 0,⟨1,1⟩⟩⟩

private theorem gap_source_accounting :
    Accounting geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical gapSource := by
  constructor
  · apply raw_shape _ rfl
    intro id active
    have choices : id = cid 0 ∨ id = cid 1 ∨ id = cid 2 := by simpa [gapSource,or_assoc] using active
    rcases choices with rfl|rfl|rfl
    · exact ⟨gapLeft,by simp [gapSource],rfl,by decide,by change 1 ≤ 4; decide⟩
    · exact ⟨right,by simp [gapSource,cid],rfl,by decide,by change 4 ≤ 4; decide⟩
    · exact ⟨⟨region 0,⟨1,1⟩⟩,by simp [gapSource,cid],rfl,by decide,by change 2 ≤ 4; decide⟩
  · intro i ia j ja neq
    have ic : i = cid 0 ∨ i = cid 1 ∨ i = cid 2 := by simpa [gapSource,or_assoc] using ia
    have jc : j = cid 0 ∨ j = cid 1 ∨ j = cid 2 := by simpa [gapSource,or_assoc] using ja
    rcases ic with rfl|rfl|rfl <;> rcases jc with rfl|rfl|rfl
    all_goals first | exact False.elim (neq rfl) | decide
  · change gapLeft.footprint geometry ∪ right.footprint geometry ∪
      (Extent.mk (region 0) ⟨1,1⟩).footprint geometry = (world rw).bytes (region 0)
    decide

theorem merge_gap_and_overlap_controls :
    Accounting geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical gapSource ∧
    ¬ RawMerge gapSource (cid 0) (cid 1) (cid 3) gapLeft right
      (mergeCandidate gapSource (cid 0) (cid 1) (cid 3) gapLeft right) ∧
    ¬ RawMerge overlapLedger (cid 1) (cid 20) (cid 3) overlapLeft right
      (mergeCandidate overlapLedger (cid 1) (cid 20) (cid 3) overlapLeft right) := by
  exact ⟨gap_source_accounting,merge_rejects_nonadjacent (by unfold Adjacent; decide),merge_rejects_nonadjacent (by unfold Adjacent; decide)⟩

private def twoRegionLedger : Ledger :=
  ⟨{region 0,region 1},{cid 1,cid 20,cid 2,cid 3},fun id =>
    if id = cid 1 then .storage left else if id = cid 20 then .storage ⟨region 1,right.range⟩
    else if id = cid 2 then .storage right else .storage ⟨region 1,left.range⟩⟩
private def twoRegionPhysical : PhysicalState :=
  ⟨{world rw with liveRegions := {region 0,region 1}},fun _ => none⟩

private theorem two_region_accounting :
    Accounting geometry layout (FlatLive rawState.flat.semantic) twoRegionPhysical twoRegionLedger := by
  have classify : ∀ i ∈ twoRegionLedger.active, i = cid 1 ∨ i = cid 20 ∨ i = cid 2 ∨ i = cid 3 := by
    intro i active; simpa [twoRegionLedger,or_assoc] using active
  have claims : ∀ i ∈ twoRegionLedger.active, ∃ e, twoRegionLedger.claim i = .storage e ∧
      e.region ∈ twoRegionLedger.scope ∧ 0 < e.range.length ∧ e.Fits geometry := by
    intro i active; rcases classify i active with rfl|rfl|rfl|rfl
    · exact ⟨left,by simp [twoRegionLedger],by decide,by decide,by change 2 ≤ 4; decide⟩
    · exact ⟨⟨region 1,right.range⟩,by simp [twoRegionLedger,cid],by decide,by decide,by change 4 ≤ 4; decide⟩
    · exact ⟨right,by simp [twoRegionLedger,cid],by decide,by decide,by change 4 ≤ 4; decide⟩
    · exact ⟨⟨region 1,left.range⟩,by simp [twoRegionLedger,cid],by decide,by decide,by change 2 ≤ 4; decide⟩
  constructor
  · constructor
    · intro r; rfl
    · intro r rl q ql different
      have rc : r = region 0 ∨ r = region 1 := by simpa [twoRegionPhysical] using rl
      have qc : q = region 0 ∨ q = region 1 := by simpa [twoRegionPhysical] using ql
      rcases rc with rfl|rfl <;> rcases qc with rfl|rfl
      all_goals first | exact False.elim (different rfl) | decide
    · intro r member; exact member
    · intro i active; rcases claims i active with ⟨e,eq,member,_,_⟩; rw [eq]; exact member
    · intro i active; rcases claims i active with ⟨e,eq,_,positive,_⟩; rw [eq]; exact positive
    · intro i active; rcases claims i active with ⟨e,eq,_,_,fits⟩; rw [eq]; exact fits
    · intro i active; rcases claims i active with ⟨e,eq,_⟩; rw [eq]; trivial
    · intro l; constructor
      · rintro ⟨r,h⟩; simp [rawState,flat,semantic] at h
      · rintro ⟨i,active,t,e,h⟩; rcases claims i active with ⟨q,eq,_⟩; rw [eq] at h; cases h
    · intro l pl; constructor
      · intro h; cases h
      · rintro ⟨i,active,t,e,h,_⟩; rcases claims i active with ⟨q,eq,_⟩; rw [eq] at h; cases h
  · intro i ia j ja different
    rcases classify i ia with rfl|rfl|rfl|rfl <;> rcases classify j ja with rfl|rfl|rfl|rfl
    all_goals first | exact False.elim (different rfl) | decide
  · change left.footprint geometry ∪ (Extent.mk (region 1) right.range).footprint geometry ∪
      right.footprint geometry ∪ (Extent.mk (region 1) left.range).footprint geometry =
      (world rw).bytes (region 0) ∪ (world rw).bytes (region 1)
    decide

/-- Complete well-formed endpoints and every raw merge guard except nominal identity. -/
theorem different_region_merge_isolates_identity :
    Accounting geometry layout (FlatLive rawState.flat.semantic) twoRegionPhysical twoRegionLedger ∧
    Has twoRegionLedger (cid 1) (.storage left) ∧
    Has twoRegionLedger (cid 20) (.storage ⟨region 1,right.range⟩) ∧
    Adjacent left.range right.range ∧
    ∀ post, ¬ RawMerge twoRegionLedger (cid 1) (cid 20) (cid 99) left ⟨region 1,right.range⟩ post := by
  exact ⟨two_region_accounting,⟨by simp [twoRegionLedger],by simp [twoRegionLedger]⟩,
    ⟨by simp [twoRegionLedger],by simp [twoRegionLedger,cid]⟩,Or.inl rfl,
    fun _ => merge_rejects_different_regions (by decide)⟩

/-- These extents are nonempty and relatively adjacent; nominal region equality is the failed guard. -/
theorem different_region_merge_control :
    0 < left.range.length ∧ 0 < right.range.length ∧ Adjacent left.range right.range ∧
    left.region ≠ (Extent.mk (region 1) right.range).region ∧
    ∀ post, ¬ RawMerge (twoRaw left ⟨region 1,right.range⟩) (cid 1) (cid 20) (cid 3)
      left ⟨region 1,right.range⟩ post :=
  ⟨by decide,by decide,Or.inl rfl,by decide,fun _ => merge_rejects_different_regions (by decide)⟩

/-- Both full Storage and an empty exact-size slot are valid endpoints separately.
The invalid proposed conversion consumes four bytes but silently accounts for only two. -/
theorem larger_into_slot_tail_control :
    WellFormed geometry layout rawState ∧ WellFormed geometry layout (slotState rw) ∧
    full.range.length > layout.size ty ∧
    ∀ post, ¬ RawIntoSlot layout True rawLedger (cid 0) (cid 3) ty full post :=
  ⟨raw_state_wellFormed,slot_state_wellFormed rw,by decide,fun _ => into_slot_rejects_larger_range (by decide)⟩

private def tailDropped : Ledger := ⟨{region 0},{cid 3},fun _ => .slot ty left⟩

theorem unchecked_into_slot_loses_tail :
    AccountingShape geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical tailDropped ∧
    NoOverlap geometry tailDropped ∧
    (⟨2⟩ : AbstractByteId) ∈ ExpectedFootprint rawState.flat.physical tailDropped ∧
    (⟨2⟩ : AbstractByteId) ∉ TotalFootprint geometry tailDropped := by
  have old := (slot_state_wellFormed rw).accounting
  refine ⟨?_,?_,?_,?_⟩
  · constructor
    · exact old.geometry
    · exact old.regions
    · exact old.scopeLive
    · intro i member; change region 0 ∈ ({region 0} : Finset BackingRegionId); simp
    · intro i member; change 0 < 2; decide
    · intro i member; change 2 ≤ 4; decide
    · intro i member; rfl
    · intro l; constructor
      · rintro ⟨r,h⟩; simp [rawState,flat,semantic] at h
      · rintro ⟨i,member,t,e,eq⟩; simp [tailDropped] at eq
    · intro l pl; constructor
      · intro h; simp [rawState,flat,physical] at h
      · rintro ⟨i,member,t,e,eq,_⟩; simp [tailDropped] at eq
  · intro i ia j ja different
    have ie : i = cid 3 := by simpa [tailDropped] using ia
    have je : j = cid 3 := by simpa [tailDropped] using ja
    exact False.elim (different (ie.trans je.symm))
  · change (⟨2⟩ : AbstractByteId) ∈ (world rw).bytes (region 0); decide
  · change (⟨2⟩ : AbstractByteId) ∉ left.footprint geometry; decide

/-- Exact splitting followed immediately by merging, in either argument order. -/
theorem split_merge_roundtrip_is_legal :
    ∃ post reverse, MergeStep geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical
      splitLedger (cid 1) (cid 20) (cid 9) left right post ∧
      MergeStep geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical
        splitLedger (cid 20) (cid 1) (cid 9) right left reverse ∧
      Has post (cid 9) (.storage full) ∧ Has reverse (cid 9) (.storage full) := by
  let forward := mergeCandidate splitLedger (cid 1) (cid 20) (cid 9) left right
  let reverse := mergeCandidate splitLedger (cid 20) (cid 1) (cid 9) right left
  have fa : Accounting geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical forward := by
    apply single_raw_accounting rw 0 {⟨0⟩} ∅ forward (cid 9)
    all_goals simp [forward,mergeCandidate,splitLedger,splitCandidate,rawLedger,cid,mergeExtent,
      mergeRange,left,right,full,Extent.left,Extent.right,Range.left,Range.right]
  have ra : Accounting geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical reverse := by
    apply single_raw_accounting rw 0 {⟨0⟩} ∅ reverse (cid 9)
    all_goals simp [reverse,mergeCandidate,splitLedger,splitCandidate,rawLedger,cid,mergeExtent,
      mergeRange,left,right,full,Extent.left,Extent.right,Range.left,Range.right] <;> decide
  have fr : RawMerge splitLedger (cid 1) (cid 20) (cid 9) left right forward :=
    ⟨split_consumes_source_and_produces_two split_is_legal.2.1 |>.2.1,
      split_consumes_source_and_produces_two split_is_legal.2.1 |>.2.2,by decide,by decide,by decide,
      rfl,Or.inl rfl,by simp [splitLedger,splitCandidate,rawLedger,cid],rfl⟩
  have rr : RawMerge splitLedger (cid 20) (cid 1) (cid 9) right left reverse :=
    ⟨fr.secondClaim,fr.firstClaim,by decide,by decide,by decide,rfl,Or.inr rfl,fr.resultFresh,rfl⟩
  refine ⟨forward,reverse,⟨split_is_legal.2.2,fr,fa⟩,⟨split_is_legal.2.2,rr,ra⟩,?_,?_⟩
  all_goals simp [Has,forward,reverse,mergeCandidate,mergeExtent,mergeRange,left,right,full,
    Extent.left,Extent.right,Range.left,Range.right]

end
end NewLang.F1.Occupancy.Counterexample
