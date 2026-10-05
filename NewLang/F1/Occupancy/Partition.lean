import NewLang.F1.Occupancy.Claims

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

/-- Exact partition preserves disjointness against every framed raw/slot/root claim,
not merely disjointness between the two outputs. -/
theorem split_preserves_no_overlap {g s source left right e k post}
    (before : NoOverlap g s) (raw : RawSplit s source left right e k post) : NoOverlap g post := by
  have part := split_extents_exact_union g (e := e) (Nat.le_of_lt raw.high)
  have ls : (e.left k).footprint g ⊆ (s.claim source).extent.footprint g := by
    rw [raw.sourceClaim.2,Claim.extent,← part]; exact Finset.subset_union_left
  have rs : (e.right k).footprint g ⊆ (s.claim source).extent.footprint g := by
    rw [raw.sourceClaim.2,Claim.extent,← part]; exact Finset.subset_union_right
  rw [raw.post_eq]
  have classify : ∀ i ∈ (splitCandidate s source left right e k).active,
      i = left ∨ i = right ∨ (i ≠ source ∧ i ∈ s.active) := by
    intro i active; simpa [splitCandidate,Finset.mem_erase,or_assoc] using active
  have frame : ∀ i ∈ s.active, (splitCandidate s source left right e k).claim i = s.claim i := by
    intro i active
    have nl : i ≠ left := fun eq => raw.leftFresh (eq ▸ active)
    have nr : i ≠ right := fun eq => raw.rightFresh (eq ▸ active)
    simp [splitCandidate,nl,nr]
  intro i ia j ja different
  rcases classify i ia with rfl|rfl|⟨ns,pre⟩
  · rcases classify j ja with rfl|rfl|⟨js,jpre⟩
    · exact False.elim (different rfl)
    · simpa [splitCandidate,raw.distinct.symm,Claim.extent] using split_extents_disjoint g e k
    · rw [frame j jpre]
      simpa [splitCandidate,Claim.extent] using
        Finset.disjoint_of_subset_left ls (before source raw.sourceClaim.1 j jpre js.symm)
  · rcases classify j ja with rfl|rfl|⟨js,jpre⟩
    · simpa [splitCandidate,raw.distinct.symm,Claim.extent] using (split_extents_disjoint g e k).symm
    · exact False.elim (different rfl)
    · rw [frame j jpre]
      simpa [splitCandidate,raw.distinct.symm,Claim.extent] using
        Finset.disjoint_of_subset_left rs (before source raw.sourceClaim.1 j jpre js.symm)
  · rw [frame i pre]
    rcases classify j ja with rfl|rfl|⟨_,jpre⟩
    · simpa [splitCandidate,Claim.extent] using
        Finset.disjoint_of_subset_right ls (before i pre source raw.sourceClaim.1 ns)
    · simpa [splitCandidate,raw.distinct.symm,Claim.extent] using
        Finset.disjoint_of_subset_right rs (before i pre source raw.sourceClaim.1 ns)
    · rw [frame j jpre]; exact before i pre j jpre different

/-- Merging adjacent inputs preserves disjointness against all framed claims. -/
theorem merge_preserves_no_overlap {g s first second result a b post}
    (before : NoOverlap g s) (raw : RawMerge s first second result a b post) : NoOverlap g post := by
  have union := (merge_preserves_identity_and_exact_union g raw).2.2.2.2
  rw [raw.post_eq]
  have classify : ∀ i ∈ (mergeCandidate s first second result a b).active,
      i = result ∨ (i ≠ second ∧ i ≠ first ∧ i ∈ s.active) := by
    intro i active; simpa [mergeCandidate,Finset.mem_erase] using active
  have frame : ∀ i ∈ s.active, (mergeCandidate s first second result a b).claim i = s.claim i := by
    intro i active
    have nr : i ≠ result := fun eq => raw.resultFresh (eq ▸ active)
    simp [mergeCandidate,nr]
  have merged_disjoint : ∀ j ∈ s.active, j ≠ first → j ≠ second →
      Disjoint ((mergeExtent a b).footprint g) ((s.claim j).extent.footprint g) := by
    intro j pre nf ns; rw [union]
    apply Finset.disjoint_union_left.mpr
    exact ⟨by simpa [raw.firstClaim.2,Claim.extent] using before first raw.firstClaim.1 j pre nf.symm,
      by simpa [raw.secondClaim.2,Claim.extent] using before second raw.secondClaim.1 j pre ns.symm⟩
  intro i ia j ja different
  rcases classify i ia with rfl|⟨ns,nf,pre⟩
  · rcases classify j ja with rfl|⟨js,jf,jpre⟩
    · exact False.elim (different rfl)
    · rw [frame j jpre]; simpa [mergeCandidate,Claim.extent] using merged_disjoint j jpre jf js
  · rw [frame i pre]
    rcases classify j ja with rfl|⟨_,_,jpre⟩
    · simpa [mergeCandidate,Claim.extent] using (merged_disjoint i pre nf ns).symm
    · rw [frame j jpre]; exact before i pre j jpre different

end
end NewLang.F1.Occupancy
