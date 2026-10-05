import NewLang.F1.Relocation.Counterexample.Accounting

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing
open Occupancy.Counterexample (geometry layout ty cid region rw)
noncomputable section

/-- All metadata/permissions precede this one atomic relation; package dependencies
are deliberately not erased by its raw structural candidate. -/
theorem raw_move (k : Case) (different : k ≠ .equal) (deps ext : Finset Conditional.Fact) :
    RawMove geometry sites ctx (before k rw deps ext) (move k)
      (moveReceipt (before k rw deps ext) (move k)) (after k rw deps ext) := by
  constructor
  · trivial
  · simp [move,before,semantic]
  · simp [Occupancy.Has,before,beforeLedger,move]
  · rfl
  · exact ⟨sumValue deps,by simp [before,semantic,move,root],by simp [Conditional.FitsAllocation,sumValue,move]⟩
  · cases k <;> first | exact False.elim (different rfl) | decide
  · change source ≠ destination; decide
  · simp [move,before,semantic,source,destination]
  · cases k <;> simp [move,before,world,regions,dstExtent,srcExtent,region]
  · cases k <;> dsimp [move,dstExtent,srcExtent,Occupancy.Extent.Fits,Occupancy.Range.finish] <;> decide
  · cases k <;> rfl
  · trivial
  · trivial
  · trivial
  · rfl
  · rfl
  · intro id member
    have eq : id = cid 1 := by simpa [move,inputIds,different] using member
    subst id
    exact ⟨inputExtent k,by simp [Occupancy.Has,before,beforeLedger,inputIds,different,cid]⟩
  · dsimp [before]; cases k <;> first | exact False.elim (different rfl) | decide
  · cases k <;> first | exact False.elim (different rfl) | decide
  · intro id _; cases k <;> dsimp [move,outputExtent,srcExtent] <;> decide
  · intro i hi j hj neq
    have ie : i = cid 3 := by simpa [move,different] using hi
    have je : j = cid 3 := by simpa [move,different] using hj
    exact False.elim (neq (ie.trans je.symm))
  · intro id member
    have eq : id = cid 3 := by simpa [move,different] using member
    subst id; cases k <;> simp [before,beforeLedger,inputIds,frameIds,cid]
  · cases k <;> simp [move,before,beforeLedger,inputIds,frameIds,cid]
  · simp [move,different,cid]
  · simp [move,before,semantic]
  · simp [Conditional.FreshAllocation,Conditional.FreshOccurrence,move,before,semantic]
  · rfl
  · rfl

theorem independent_move_is_legal (k : Case) (different : k ≠ .equal) :
    Step geometry layout sites ctx (before k rw ∅ ∅) (.move (move k))
      (moveReceipt (before k rw ∅ ∅) (move k)) (after k rw ∅ ∅) :=
  ⟨independent_before_wellFormed k rw,.move (raw_move k different ∅ ∅),independent_after_wellFormed k rw⟩

theorem disjoint_relocation_is_legal :
    Step geometry layout sites ctx (before .disjoint rw ∅ ∅) (.move (move .disjoint))
      (moveReceipt (before .disjoint rw ∅ ∅) (move .disjoint)) (after .disjoint rw ∅ ∅) := independent_move_is_legal .disjoint (by decide)
theorem overlapping_relocation_is_legal :
    Step geometry layout sites ctx (before .overlap rw ∅ ∅) (.move (move .overlap))
      (moveReceipt (before .overlap rw ∅ ∅) (move .overlap)) (after .overlap rw ∅ ∅) := independent_move_is_legal .overlap (by decide)
theorem different_region_relocation_is_legal :
    Step geometry layout sites ctx (before .different rw ∅ ∅) (.move (move .different))
      (moveReceipt (before .different rw ∅ ∅) (move .different)) (after .different rw ∅ ∅) := independent_move_is_legal .different (by decide)

/-- Exactly S-D, S∩D and D-S; the old frame claim remains a value-owned Storage. -/
theorem partial_overlap_three_responsibilities :
    sourceBytes geometry (move .overlap) \ destinationBytes geometry (move .overlap) = {⟨0⟩} ∧
    sourceBytes geometry (move .overlap) ∩ destinationBytes geometry (move .overlap) = {⟨1⟩} ∧
    destinationBytes geometry (move .overlap) \ sourceBytes geometry (move .overlap) = {⟨2⟩} ∧
    Occupancy.Has (after .overlap rw ∅ ∅).accounted.ledger (cid 3) (.storage (outputExtent .overlap)) ∧
    cid 1 ∉ (after .overlap rw ∅ ∅).accounted.ledger.active ∧
    (after .overlap rw ∅ ∅).accounted.ledger.claim (cid 2) = (before .overlap rw ∅ ∅).accounted.ledger.claim (cid 2) := by
  unfold Occupancy.Has
  decide

theorem package_with_embedded_ptr_and_owned_storage_transfers_once :
    ((after .overlap rw ∅ ∅).accounted.base.semantic.root destination).package = pkg ∧
    (after .overlap rw ∅ ∅).data pkg = (before .overlap rw ∅ ∅).data pkg ∧
    ((after .overlap rw ∅ ∅).data pkg).persistentPtrs = [⟨source,⟨0⟩⟩] ∧
    ¬ CurrentToken (after .overlap rw ∅ ∅) ⟨source,⟨0⟩⟩ ∧
    CurrentToken (after .overlap rw ∅ ∅) ⟨destination,⟨1⟩⟩ := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · exact (raw_move .overlap (by decide) ∅ ∅).old_token_stale
  · exact (raw_move .overlap (by decide) ∅ ∅).fresh_destination_token.1

/-- Dependence on the actual active source occurrence is legal before relocation. -/
theorem before_occurrence_dependencies_valid (k : Case) (a : Access) (deps ext : Finset Conditional.Fact)
    (d : deps ⊆ {.occurrence ⟨0⟩}) (e : ext ⊆ {.occurrence ⟨0⟩}) :
    Conditional.DependenciesValid (before k a deps ext).accounted.base.semantic := by
  have live : Conditional.Fact.occurrence ⟨0⟩ ∈ Conditional.LiveFacts (semantic deps ext) :=
    ⟨source,by simp [semantic],rfl⟩
  intro p _ v present f dep
  by_cases same : p = pkg
  · subst p
    have ve : v = .sum (sumValue deps) := by simpa [before,semantic] using present.symm
    subst v
    have fd : f ∈ deps := by simpa [Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies,sumValue] using dep
    have eq : f = .occurrence ⟨0⟩ := by simpa using d fd
    exact eq ▸ live
  · have ve : v = externalValue ext := by simpa [before,semantic,same] using present.symm
    subst v
    have fe : f ∈ ext := dep
    have eq : f = .occurrence ⟨0⟩ := by simpa using e fe
    exact eq ▸ live

theorem before_occurrence_wellFormed (k : Case) (a : Access) (deps ext : Finset Conditional.Fact)
    (d : deps ⊆ {.occurrence ⟨0⟩}) (e : ext ⊆ {.occurrence ⟨0⟩}) :
    WellFormed geometry layout (before k a deps ext) := by
  have wf := independent_before_wellFormed k a
  exact ⟨⟨before_invariant deps ext,before_occurrence_dependencies_valid k a deps ext d e,wf.accounting⟩,
    wf.ownedPresent,wf.ownedUnique⟩

theorem same_place_requires_no_ending_or_read_write :
    Step geometry layout sites noAuthority (before .equal ⟨false,false⟩ {.occurrence ⟨0⟩} ∅)
      (.same source (cid 0) ty srcExtent) .identity (before .equal ⟨false,false⟩ {.occurrence ⟨0⟩} ∅) := by
  apply same_place_is_legal
  · exact before_occurrence_wellFormed _ _ _ _ (by simp) (by simp)
  · trivial
  · simp [before,semantic]
  · simp [Occupancy.Has,before,beforeLedger]

theorem source_occurrence_dependency_rejects_move :
    ¬ Step geometry layout sites ctx (before .overlap rw {.occurrence ⟨0⟩} ∅) (.move (move .overlap))
      (moveReceipt (before .overlap rw {.occurrence ⟨0⟩} ∅) (move .overlap))
      (after .overlap rw {.occurrence ⟨0⟩} ∅) := by
  apply move_rejects_surviving_old_occurrence_dependency
    (before_occurrence_wellFormed _ _ _ _ (by simp) (by simp)) (pkg := pkg) (value := .sum (sumValue {.occurrence ⟨0⟩}))
  · exact Or.inr ⟨source,by simp [before,semantic],rfl⟩
  · simp [before,semantic]
  · rfl
  · simp [Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies,sumValue]

theorem external_occurrence_dependency_rejects_move :
    ¬ Step geometry layout sites ctx (before .overlap rw ∅ {.occurrence ⟨0⟩}) (.move (move .overlap))
      (moveReceipt (before .overlap rw ∅ {.occurrence ⟨0⟩}) (move .overlap))
      (after .overlap rw ∅ {.occurrence ⟨0⟩}) := by
  apply move_rejects_surviving_old_occurrence_dependency
    (before_occurrence_wellFormed _ _ _ _ (by simp) (by simp)) (pkg := external) (value := externalValue {.occurrence ⟨0⟩})
  · exact Or.inl (by simp [before,semantic])
  · simp [before,semantic,pkg,external]
  · rfl
  · simp [externalValue,Conditional.SemanticValue.dependencies]

end
end NewLang.F1.Relocation.Counterexample
