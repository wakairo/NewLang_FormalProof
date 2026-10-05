import NewLang.F1.Occupancy.Model

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

/-- Atomic consume/produce at authority carriers. Inactive table records grant
no responsibility. These are ghost carrier choices, not runtime token allocation. -/
def consumeOne (s : Ledger) (source result : ClaimId) (new : Claim) : Ledger :=
  {s with active := insert result (s.active.erase source)
          claim := fun id => if id = result then new else s.claim id}

def splitCandidate (s : Ledger) (source left right : ClaimId) (e : Extent) (k : Nat) : Ledger :=
  {s with active := insert left (insert right (s.active.erase source))
          claim := fun id => if id = left then .storage (e.left k)
            else if id = right then .storage (e.right k) else s.claim id}

def mergeCandidate (s : Ledger) (first second result : ClaimId) (a b : Extent) : Ledger :=
  {s with active := insert result ((s.active.erase first).erase second)
          claim := fun id => if id = result then .storage (mergeExtent a b) else s.claim id}

structure RawSplit (s : Ledger) (source left right : ClaimId) (e : Extent) (k : Nat) (post : Ledger) : Prop where
  sourceClaim : Has s source (.storage e)
  low : 0 < k
  high : k < e.range.length
  leftFresh : left ∉ s.active
  rightFresh : right ∉ s.active
  distinct : left ≠ right
  post_eq : post = splitCandidate s source left right e k

structure RawMerge (s : Ledger) (first second result : ClaimId) (a b : Extent) (post : Ledger) : Prop where
  firstClaim : Has s first (.storage a)
  secondClaim : Has s second (.storage b)
  distinct : first ≠ second
  positiveLeft : 0 < a.range.length
  positiveRight : 0 < b.range.length
  sameRegion : a.region = b.region
  adjacent : Adjacent a.range b.range
  resultFresh : result ∉ s.active
  post_eq : post = mergeCandidate s first second result a b

structure RawIntoSlot (layout : Layout) (aligned : Prop) (s : Ledger)
    (source result : ClaimId) (t : TypeId) (e : Extent) (post : Ledger) : Prop where
  sourceClaim : Has s source (.storage e)
  resultFresh : result ∉ s.active
  exactSize : e.range.length = layout.size t
  alignment : aligned
  post_eq : post = consumeOne s source result (.slot t e)

/-- No backing read/write condition: valid definitely-empty slot conversion is safe. -/
structure RawEraseSlot (s : Ledger) (source result : ClaimId) (t : TypeId) (e : Extent) (post : Ledger) : Prop where
  sourceClaim : Has s source (.slot t e)
  resultFresh : result ∉ s.active
  post_eq : post = consumeOne s source result (.storage e)

def SplitStep (g : Geometry) (layout : Layout) (live : RootLocationId → Prop) (p : PhysicalState)
    (s : Ledger) (source left right : ClaimId) (e : Extent) (k : Nat) (post : Ledger) : Prop :=
  Accounting g layout live p s ∧ RawSplit s source left right e k post ∧ Accounting g layout live p post

def MergeStep (g : Geometry) (layout : Layout) (live : RootLocationId → Prop) (p : PhysicalState)
    (s : Ledger) (first second result : ClaimId) (a b : Extent) (post : Ledger) : Prop :=
  Accounting g layout live p s ∧ RawMerge s first second result a b post ∧ Accounting g layout live p post

def IntoSlotStep (g : Geometry) (layout : Layout) (aligned : Prop)
    (live : RootLocationId → Prop) (p : PhysicalState)
    (s : Ledger) (source result : ClaimId) (t : TypeId) (e : Extent) (post : Ledger) : Prop :=
  Accounting g layout live p s ∧ RawIntoSlot layout aligned s source result t e post ∧
    Accounting g layout live p post

def EraseSlotStep (g : Geometry) (layout : Layout) (live : RootLocationId → Prop) (p : PhysicalState)
    (s : Ledger) (source result : ClaimId) (t : TypeId) (e : Extent) (post : Ledger) : Prop :=
  Accounting g layout live p s ∧ RawEraseSlot s source result t e post ∧ Accounting g layout live p post

theorem consumeOne_active_iff {s : Ledger} {source result id : ClaimId} {new : Claim} :
    id ∈ (consumeOne s source result new).active ↔ id = result ∨ (id ≠ source ∧ id ∈ s.active) := by
  simp [consumeOne,Finset.mem_erase]

theorem consumeOne_consumes_source {s : Ledger} {source result : ClaimId} {new : Claim}
    (active : source ∈ s.active) (fresh : result ∉ s.active) :
    source ∉ (consumeOne s source result new).active := by
  have different : source ≠ result := fun eq => fresh (eq ▸ active)
  simp [consumeOne,different]

theorem consumeOne_produces_result (s : Ledger) (source result : ClaimId) (new : Claim) :
    Has (consumeOne s source result new) result new := ⟨by simp [consumeOne],by simp [consumeOne]⟩

/-- Local finite-ledger equality, reused by the two empty-claim conversions and
lifetime wrappers. No general transition/effect framework is introduced. -/
theorem consumeOne_conserves_footprint (g : Geometry) {s : Ledger} {source result : ClaimId}
    {new : Claim} (active : source ∈ s.active) (fresh : result ∉ s.active)
    (same : new.extent.footprint g = (s.claim source).extent.footprint g) :
    TotalFootprint g (consumeOne s source result new) = TotalFootprint g s := by
  ext byte; constructor
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    rcases consumeOne_active_iff.mp ia with rfl | ⟨other,pre⟩
    · have newMem : byte ∈ new.extent.footprint g := by simpa [consumeOne] using im
      exact Finset.mem_biUnion.mpr ⟨source,active,same ▸ newMem⟩
    · have notResult : id ≠ result := fun eq => fresh (eq ▸ pre)
      exact Finset.mem_biUnion.mpr ⟨id,pre,by simpa [consumeOne,notResult] using im⟩
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    by_cases src : id = source
    · subst id
      refine Finset.mem_biUnion.mpr ⟨result,by simp [consumeOne],?_⟩
      simpa only [consumeOne,ite_true] using same.symm ▸ im
    · have notResult : id ≠ result := fun eq => fresh (eq ▸ ia)
      exact Finset.mem_biUnion.mpr ⟨id,consumeOne_active_iff.mpr (Or.inr ⟨src,ia⟩),
        by simpa [consumeOne,notResult] using im⟩

section Split
variable {s post : Ledger} {source left right : ClaimId} {e : Extent} {k : Nat}

theorem split_consumes_source_and_produces_two (raw : RawSplit s source left right e k post) :
    source ∉ post.active ∧ Has post left (.storage (e.left k)) ∧ Has post right (.storage (e.right k)) := by
  have sl : source ≠ left := fun eq => raw.leftFresh (eq ▸ raw.sourceClaim.1)
  have sr : source ≠ right := fun eq => raw.rightFresh (eq ▸ raw.sourceClaim.1)
  rw [raw.post_eq]
  exact ⟨by simp [splitCandidate,sl,sr],⟨by simp [splitCandidate],by simp [splitCandidate]⟩,
    ⟨by simp [splitCandidate],by simp [splitCandidate,raw.distinct.symm]⟩⟩

theorem split_preserves_identity_nonempty_partition (g : Geometry) (raw : RawSplit s source left right e k post) :
    (e.left k).region = e.region ∧ (e.right k).region = e.region ∧
    0 < (e.left k).range.length ∧ 0 < (e.right k).range.length ∧
    Disjoint ((e.left k).footprint g) ((e.right k).footprint g) ∧
    (e.left k).footprint g ∪ (e.right k).footprint g = e.footprint g :=
  ⟨rfl,rfl,(split_ranges_are_nonempty raw.low raw.high).1,
    (split_ranges_are_nonempty raw.low raw.high).2,split_extents_disjoint g e k,
    split_extents_exact_union g (Nat.le_of_lt raw.high)⟩

theorem split_rejects_left_endpoint : ¬ RawSplit s source left right e 0 post := by
  intro raw; exact Nat.lt_irrefl 0 raw.low

theorem split_rejects_right_endpoint : ¬ RawSplit s source left right e e.range.length post := by
  intro raw; exact Nat.lt_irrefl _ raw.high

theorem split_conserves_all_byte_responsibility (g : Geometry) (raw : RawSplit s source left right e k post) :
    TotalFootprint g post = TotalFootprint g s := by
  rw [raw.post_eq]
  have partition := split_extents_exact_union g (e := e) (Nat.le_of_lt raw.high)
  ext byte; constructor
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    have cases : id = left ∨ id = right ∨ (id ≠ source ∧ id ∈ s.active) := by
      simpa [splitCandidate,Finset.mem_erase,or_assoc] using ia
    rcases cases with rfl|rfl|⟨_,pre⟩
    · have lm : byte ∈ (e.left k).footprint g := by simpa [splitCandidate,Claim.extent] using im
      exact Finset.mem_biUnion.mpr ⟨source,raw.sourceClaim.1,by
        rw [raw.sourceClaim.2,Claim.extent,← partition]; exact Finset.mem_union_left _ lm⟩
    · have rm : byte ∈ (e.right k).footprint g := by simpa [splitCandidate,raw.distinct.symm,Claim.extent] using im
      exact Finset.mem_biUnion.mpr ⟨source,raw.sourceClaim.1,by
        rw [raw.sourceClaim.2,Claim.extent,← partition]; exact Finset.mem_union_right _ rm⟩
    · have nl : id ≠ left := fun eq => raw.leftFresh (eq ▸ pre)
      have nr : id ≠ right := fun eq => raw.rightFresh (eq ▸ pre)
      exact Finset.mem_biUnion.mpr ⟨id,pre,by simpa [splitCandidate,nl,nr] using im⟩
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    by_cases old : id = source
    · subst id; rw [raw.sourceClaim.2,Claim.extent,← partition] at im
      rcases Finset.mem_union.mp im with lm|rm
      · exact Finset.mem_biUnion.mpr ⟨left,by simp [splitCandidate],by simpa [splitCandidate,Claim.extent] using lm⟩
      · exact Finset.mem_biUnion.mpr ⟨right,by simp [splitCandidate],by simpa [splitCandidate,Claim.extent,raw.distinct.symm] using rm⟩
    · have nl : id ≠ left := fun eq => raw.leftFresh (eq ▸ ia)
      have nr : id ≠ right := fun eq => raw.rightFresh (eq ▸ ia)
      exact Finset.mem_biUnion.mpr ⟨id,by simp [splitCandidate,old,ia],by simpa [splitCandidate,nl,nr] using im⟩

theorem split_preserves_scope (raw : RawSplit s source left right e k post) : post.scope = s.scope := by
  rw [raw.post_eq]; rfl
end Split

section Merge
variable {s post : Ledger} {first second result : ClaimId} {a b : Extent}

theorem merge_consumes_both_inputs (raw : RawMerge s first second result a b post) :
    first ∉ post.active ∧ second ∉ post.active ∧ Has post result (.storage (mergeExtent a b)) := by
  have f : first ≠ result := fun eq => raw.resultFresh (eq ▸ raw.firstClaim.1)
  have t : second ≠ result := fun eq => raw.resultFresh (eq ▸ raw.secondClaim.1)
  rw [raw.post_eq]
  exact ⟨by simp [mergeCandidate,f],by simp [mergeCandidate,t],
    ⟨by simp [mergeCandidate],by simp [mergeCandidate]⟩⟩

theorem merge_preserves_identity_and_exact_union (g : Geometry) (raw : RawMerge s first second result a b post) :
    (mergeExtent a b).region = a.region ∧ (mergeExtent a b).region = b.region ∧
    0 < (mergeExtent a b).range.length ∧ Disjoint (a.footprint g) (b.footprint g) ∧
    (mergeExtent a b).footprint g = a.footprint g ∪ b.footprint g :=
  ⟨rfl,raw.sameRegion,by change 0 < a.range.length + b.range.length; have positive := raw.positiveLeft; omega,
    adjacent_extents_disjoint g raw.sameRegion raw.adjacent,
    (adjacent_extents_exact_union g raw.sameRegion raw.positiveLeft raw.positiveRight raw.adjacent).symm⟩

theorem merge_rejects_different_regions (different : a.region ≠ b.region) :
    ¬ RawMerge s first second result a b post := fun raw => different raw.sameRegion

theorem merge_rejects_nonadjacent (gapOrOverlap : ¬ Adjacent a.range b.range) :
    ¬ RawMerge s first second result a b post := fun raw => gapOrOverlap raw.adjacent

theorem merge_conserves_all_byte_responsibility (g : Geometry) (raw : RawMerge s first second result a b post) :
    TotalFootprint g post = TotalFootprint g s := by
  rw [raw.post_eq]
  have union := (merge_preserves_identity_and_exact_union g raw).2.2.2.2
  ext byte; constructor
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    have cases : id = result ∨ (id ≠ second ∧ id ≠ first ∧ id ∈ s.active) := by
      simpa [mergeCandidate,Finset.mem_erase] using ia
    rcases cases with rfl|⟨_,_,pre⟩
    · have merged : byte ∈ (mergeExtent a b).footprint g := by simpa [mergeCandidate,Claim.extent] using im
      rw [union] at merged
      rcases Finset.mem_union.mp merged with fm|sm
      · exact Finset.mem_biUnion.mpr ⟨first,raw.firstClaim.1,by simpa [raw.firstClaim.2,Claim.extent] using fm⟩
      · exact Finset.mem_biUnion.mpr ⟨second,raw.secondClaim.1,by simpa [raw.secondClaim.2,Claim.extent] using sm⟩
    · have nr : id ≠ result := fun eq => raw.resultFresh (eq ▸ pre)
      exact Finset.mem_biUnion.mpr ⟨id,pre,by simpa [mergeCandidate,nr] using im⟩
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨id,ia,im⟩
    by_cases f : id = first
    · subst id
      exact Finset.mem_biUnion.mpr ⟨result,by simp [mergeCandidate],by
        simpa [mergeCandidate,Claim.extent,union] using Finset.mem_union_left (b.footprint g)
          (show byte ∈ a.footprint g by simpa [raw.firstClaim.2,Claim.extent] using im)⟩
    · by_cases t : id = second
      · subst id
        exact Finset.mem_biUnion.mpr ⟨result,by simp [mergeCandidate],by
          simpa [mergeCandidate,Claim.extent,union] using Finset.mem_union_right (a.footprint g)
            (show byte ∈ b.footprint g by simpa [raw.secondClaim.2,Claim.extent] using im)⟩
      · have nr : id ≠ result := fun eq => raw.resultFresh (eq ▸ ia)
        exact Finset.mem_biUnion.mpr ⟨id,by simp [mergeCandidate,f,t,ia],by simpa [mergeCandidate,nr] using im⟩
end Merge

section Conversion
variable {s post : Ledger} {source result : ClaimId} {t : TypeId} {e : Extent}

theorem into_slot_consumes_raw_exact_range {layout : Layout} {aligned : Prop}
    (raw : RawIntoSlot layout aligned s source result t e post) :
    source ∉ post.active ∧ Has post result (.slot t e) ∧ e.range.length = layout.size t := by
  rw [raw.post_eq]
  exact ⟨consumeOne_consumes_source raw.sourceClaim.1 raw.resultFresh,
    consumeOne_produces_result _ _ _ _,raw.exactSize⟩

theorem into_slot_rejects_larger_range {layout : Layout} {aligned : Prop}
    (larger : layout.size t < e.range.length) : ¬ RawIntoSlot layout aligned s source result t e post := by
  intro raw; rw [raw.exactSize] at larger; exact Nat.lt_irrefl _ larger

theorem into_slot_conserves_all_byte_responsibility (g : Geometry) {layout : Layout} {aligned : Prop}
    (raw : RawIntoSlot layout aligned s source result t e post) : TotalFootprint g post = TotalFootprint g s := by
  rw [raw.post_eq]; apply consumeOne_conserves_footprint g raw.sourceClaim.1 raw.resultFresh
  rw [raw.sourceClaim.2]; rfl

theorem erase_slot_consumes_empty_exact_range (raw : RawEraseSlot s source result t e post) :
    source ∉ post.active ∧ Has post result (.storage e) := by
  rw [raw.post_eq]; exact ⟨consumeOne_consumes_source raw.sourceClaim.1 raw.resultFresh,consumeOne_produces_result _ _ _ _⟩

theorem erase_slot_conserves_all_byte_responsibility (g : Geometry)
    (raw : RawEraseSlot s source result t e post) : TotalFootprint g post = TotalFootprint g s := by
  rw [raw.post_eq]; apply consumeOne_conserves_footprint g raw.sourceClaim.1 raw.resultFresh
  rw [raw.sourceClaim.2]; rfl



theorem erase_slot_has_no_access_precondition (sourceClaim : Has s source (.slot t e)) :
    ∃ result post, RawEraseSlot s source result t e post := by
  rcases Finset.exists_nat_subset_range (s.active.image ClaimId.index) with ⟨n,bound⟩
  have fresh : (⟨n⟩ : ClaimId) ∉ s.active := by
    intro member
    have inside := bound (Finset.mem_image.mpr ⟨⟨n⟩,member,rfl⟩)
    exact Nat.lt_irrefl n (Finset.mem_range.mp inside)
  exact ⟨⟨n⟩,_,sourceClaim,fresh,rfl⟩

end Conversion

end
end NewLang.F1.Occupancy
