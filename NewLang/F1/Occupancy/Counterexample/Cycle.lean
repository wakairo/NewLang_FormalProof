import NewLang.F1.Occupancy.Counterexample.Fixtures

namespace NewLang.F1.Occupancy.Counterexample
open F0 Backing
noncomputable section

private theorem pair_wf (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId) (c : Claim)
    (scope : s.scope = {region 0}) (ids : s.active = {id,cid 20}) (different : id ≠ cid 20)
    (lc : s.claim id = c) (rc : s.claim (cid 20) = .storage right)
    (extent : c.extent = left) (typed : c.Typed layout)
    (rootClaim : ∀ t l e, c = .root t l e ↔ active = true ∧ t = ty ∧ l = ⟨0⟩ ∧ e = left)
    (unique : active = true → (⟨0⟩ : PackageId) ∉ loose) (recorded : active = true → n ∈ history) :
    WellFormed geometry layout ⟨flat a active n loose history,s⟩ :=
  ⟨semantic_wf _ _ _ _ unique recorded,
    pair_accounting a active n loose history s id c scope ids different lc rc extent typed rootClaim⟩

/-- A full-region single raw claim also represents the merged endpoint. -/
theorem single_raw_accounting (a : Access) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId)
    (scope : s.scope = {region 0}) (ids : s.active = {id}) (data : s.claim id = .storage full) :
    Accounting geometry layout (FlatLive (semantic false n loose history)) (physical a false) s := by
  have classify : ∀ i ∈ s.active, i = id := by intro i h; simpa [ids] using h
  constructor
  · constructor
    · intro r; rfl
    · intro r rl q ql neq
      exact False.elim (neq ((Finset.mem_singleton.mp rl).trans (Finset.mem_singleton.mp ql).symm))
    · intro r member; simpa [scope,physical,world] using member
    · intro i member; rw [classify i member,data,scope]; exact Finset.mem_singleton_self _
    · intro i member; rw [classify i member,data]; decide
    · intro i member; rw [classify i member,data]; change 4 ≤ 4; decide
    · intro i member; rw [classify i member,data]; trivial
    · intro l; constructor
      · rintro ⟨r,h⟩; simp [semantic] at h
      · rintro ⟨i,member,t,e,claim⟩; rw [classify i member,data] at claim; cases claim
    · intro l pl; constructor
      · intro h; simp [physical] at h
      · rintro ⟨i,member,t,e,claim,_⟩; rw [classify i member,data] at claim; cases claim
  · intro i ia j ja neq; exact False.elim (neq ((classify i ia).trans (classify j ja).symm))
  · simp [TotalFootprint,ExpectedFootprint,ids,scope,data,physical,world,Claim.extent,
      Extent.footprint,full,Range.positions,Range.finish]

theorem raw_state_wellFormed : WellFormed geometry layout rawState :=
  ⟨semantic_wf _ _ _ _ (by simp) (by simp),single_raw_accounting rw 0 {⟨0⟩} ∅ rawLedger (cid 0) rfl rfl rfl⟩

theorem split_is_legal :
    SplitStep geometry layout (FlatLive rawState.flat.semantic) rawState.flat.physical
      rawLedger (cid 0) (cid 1) (cid 20) full 2 splitLedger := by
  refine ⟨raw_state_wellFormed.accounting,⟨⟨by simp [rawLedger],rfl⟩,by decide,by decide,
    by simp [rawLedger,cid],by simp [rawLedger,cid],by decide,rfl⟩,?_⟩
  apply pair_accounting rw false 0 {⟨0⟩} ∅ splitLedger (cid 1) (.storage left)
  all_goals simp [splitLedger,splitCandidate,rawLedger,cid,Claim.extent,Claim.Typed,left,right]

theorem slot_state_wellFormed (a : Access) : WellFormed geometry layout (slotState a) := by
  apply pair_wf a false 0 {⟨0⟩} ∅ slotLedger (cid 3) (.slot ty left)
  all_goals simp [slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid,Claim.extent,
    Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

theorem into_slot_is_legal :
    IntoSlotStep geometry layout True (FlatLive rawState.flat.semantic) rawState.flat.physical
      splitLedger (cid 1) (cid 3) ty left slotLedger := by
  apply into_slot_step_of_raw split_is_legal.2.2
  exact ⟨(split_consumes_source_and_produces_two split_is_legal.2.1).2.1,
    by simp [splitLedger,splitCandidate,rawLedger,cid],rfl,trivial,rfl⟩

theorem first_wellFormed (a : Access) : WellFormed geometry layout (first a) := by
  apply pair_wf a true 1 ∅ {1} liveLedger (cid 4) (.root ty ⟨0⟩ left)
  all_goals simp [liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid,
    Claim.extent,Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

theorem taken_wellFormed (a : Access) : WellFormed geometry layout (taken a) := by
  apply pair_wf a false 1 {⟨0⟩} {1} takenLedger (cid 5) (.slot ty left)
  all_goals simp [takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid,
    Claim.extent,Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

theorem restart_wellFormed : WellFormed geometry layout restarted := by
  apply pair_wf rw true 2 ∅ {1,2} restartLedger (cid 6) (.root ty ⟨0⟩ left)
  all_goals simp [restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,
    rawLedger,cid,Claim.extent,Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

theorem ended_wellFormed : WellFormed geometry layout ended := by
  apply pair_wf rw false 2 ∅ {1,2} endLedger (cid 7) (.slot ty left)
  all_goals simp [endLedger,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,
    rawLedger,cid,Claim.extent,Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

private theorem first_raw (a : Access) (write : a.write = true) :
    RawInitialize geometry sites True True (slotState a) (cid 3) (cid 4) ty left ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩
      (evidence a) (first a) := by
  constructor
  · simp [Has,slotState,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · simp [slotState,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · constructor
    · refine ⟨rfl,by simp [slotState,flat,semantic],by simp [slotState,flat,semantic],?_,?_,trivial,trivial,?_⟩
      · simp [FreshIncarnation,slotState,flat,semantic]
      · simp [FreshValueFact,slotState,flat,semantic]
      · simp [first,slotState,flat,semantic,initializeCandidate,root,initializeRoot,sites]
    · exact ⟨by simp [slotState,flat,physical,world,evidence],accessLe_refl a⟩
    · rfl
    · exact write
    · exact fitting_extent_is_inside_backing (by intro r; rfl) (by change 2 ≤ 4; decide)
    · intro m pl placed; simp [slotState,flat,physical] at placed
    · simp [first,slotState,flat,physical,startPlacement]
  · rfl

theorem initialize_is_legal (a : Access) (write : a.write = true) :
    InitializeStep geometry layout sites True True (slotState a) (cid 3) (cid 4) ty left
      ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩ (evidence a) (first a) :=
  ⟨slot_state_wellFormed a,first_raw a write,first_wellFormed a⟩

private theorem first_current (a : Access) (write : a.write = true) :
    CurrentAccessPtr (first a).flat (ptr a) := Backing.initialize_produces_current_ptr (first_raw a write).backing

private theorem take_raw : RawTake True (first rw) (cid 4) (cid 5) ty left ⟨0⟩ (root 1) ⟨0⟩ (ptr rw) (taken rw) := by
  refine ⟨?_,?_,?_,rfl⟩
  · simp [Has,first,liveLedger,consumeOne]
  · simp [first,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · refine ⟨⟨by simp [first,flat,semantic],rfl,trivial,?_⟩,rfl,first_current rw rfl,rfl,?_⟩
    · simp [taken,first,flat,semantic,takeCandidate,root,initializeRoot,sites]
      funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
    · simp [taken,first,flat,physical,endPlacement]
      funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]

theorem take_is_legal :
    TakeStep geometry layout True (first rw) (cid 4) (cid 5) ty left ⟨0⟩ (root 1) ⟨0⟩ (ptr rw) (taken rw) :=
  ⟨first_wellFormed rw,take_raw,taken_wellFormed rw⟩

private theorem restart_raw :
    RawInitialize geometry sites True True (taken rw) (cid 5) (cid 6) ty left ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (evidence rw) restarted := by
  constructor
  · simp [Has,taken,takenLedger,consumeOne]
  · simp [taken,takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · constructor
    · refine ⟨rfl,by simp [taken,flat,semantic],by simp [taken,flat,semantic],?_,?_,trivial,trivial,?_⟩
      · simp [FreshIncarnation,taken,flat,semantic]
      · simp [FreshValueFact,taken,flat,semantic]
      · simp [restarted,taken,flat,semantic,initializeCandidate,root,initializeRoot,sites,Finset.pair_comm]
    · exact ⟨by simp [taken,flat,physical,world,evidence],accessLe_refl rw⟩
    · rfl
    · rfl
    · exact fitting_extent_is_inside_backing (by intro r; rfl) (by change 2 ≤ 4; decide)
    · intro m pl placed; simp [taken,flat,physical] at placed
    · simp [restarted,taken,flat,physical,startPlacement]
  · rfl

theorem same_range_restart_is_legal_and_old_ptr_stays_stale :
    InitializeStep geometry layout sites True True (taken rw) (cid 5) (cid 6) ty left
      ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩ (evidence rw) restarted ∧ ¬ CurrentAccessPtr restarted.flat (ptr rw) :=
  ⟨⟨taken_wellFormed rw,restart_raw,restart_wellFormed⟩,
    take_then_same_range_restart_rejects_stale_ptr (first_wellFormed rw) take_raw restart_raw⟩

private theorem destroy_raw :
    RawDestroy True restarted (cid 6) (cid 7) ty left ⟨0⟩ (root 2) ⟨0⟩ secondPtr ended := by
  refine ⟨?_,?_,?_,rfl⟩
  · simp [Has,restarted,restartLedger,consumeOne]
  · simp [restarted,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
  · refine ⟨⟨by simp [restarted,flat,semantic],rfl,trivial,⟨data,rfl,rfl⟩,?_⟩,rfl,
      Backing.initialize_produces_current_ptr restart_raw.backing,?_⟩
    · simp [ended,restarted,flat,semantic,destroyCandidate,root,initializeRoot,sites]
      funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
    · simp [ended,restarted,flat,physical,endPlacement]
      funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]

theorem destroy_is_legal :
    DestroyStep geometry layout True restarted (cid 6) (cid 7) ty left ⟨0⟩ (root 2) ⟨0⟩ secondPtr ended :=
  ⟨restart_wellFormed,destroy_raw,ended_wellFormed⟩

theorem erase_slot_is_legal :
    EraseSlotStep geometry layout (FlatLive ended.flat.semantic) ended.flat.physical
      endLedger (cid 7) (cid 8) ty left erasedLedger := by
  apply erase_slot_step_of_raw (s := endLedger) ended_wellFormed.accounting
  exact ⟨⟨by simp [endLedger,consumeOne],by simp [endLedger,consumeOne]⟩,
    by simp [endLedger,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid],rfl⟩

theorem merged_wellFormed : WellFormed geometry layout merged := by
  refine ⟨semantic_wf _ _ _ _ (by simp) (by simp),?_⟩
  apply single_raw_accounting rw 2 ∅ {1,2} mergedLedger (cid 9)
  all_goals simp [mergedLedger,erasedLedger,endLedger,restartLedger,takenLedger,liveLedger,slotLedger,
    consumeOne,mergeCandidate,splitLedger,splitCandidate,rawLedger,cid,mergeExtent,mergeRange,left,right,
    full,Extent.left,Extent.right,Range.left,Range.right]

theorem merge_after_lifecycle_is_legal :
    MergeStep geometry layout (FlatLive ended.flat.semantic) ended.flat.physical
      erasedLedger (cid 8) (cid 20) (cid 9) left right mergedLedger := by
  refine ⟨erase_slot_is_legal.2.2,?_,merged_wellFormed.accounting⟩
  constructor
  · simp [Has,erasedLedger,consumeOne]
  · simp [Has,erasedLedger,endLedger,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,
      splitLedger,splitCandidate,rawLedger,cid,right]
  · decide
  · decide
  · decide
  · rfl
  · exact Or.inl rfl
  · simp [erasedLedger,endLedger,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,
      splitLedger,splitCandidate,rawLedger,cid]
  · rfl

def destroyedWriteonly : State := ⟨flat wo false 1 ∅ {1},takenLedger⟩

theorem writeonly_destroy_is_legal :
    DestroyStep geometry layout True (first wo) (cid 4) (cid 5) ty left
      ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) destroyedWriteonly := by
  refine ⟨first_wellFormed wo,?_,?_⟩
  · refine ⟨?_,?_,?_,rfl⟩
    · simp [Has,first,liveLedger,consumeOne]
    · simp [first,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid]
    · refine ⟨⟨by simp [first,flat,semantic],rfl,trivial,⟨data,rfl,rfl⟩,?_⟩,
        rfl,first_current wo rfl,?_⟩
      · simp [destroyedWriteonly,first,flat,semantic,destroyCandidate,root,initializeRoot,sites]
        funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
      · simp [destroyedWriteonly,first,flat,physical,endPlacement]
        funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
  · apply pair_wf wo false 1 ∅ {1} takenLedger (cid 5) (.slot ty left)
    all_goals simp [takenLedger,liveLedger,slotLedger,consumeOne,splitLedger,splitCandidate,rawLedger,cid,
      Claim.extent,Claim.Typed,ty,layout,left,full,Extent.left,Range.left,right,Extent.right,Range.right,eq_comm]

theorem writeonly_take_rejected_but_destroy_allowed :
    ¬ RawTake True (first wo) (cid 4) (cid 5) ty left ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (taken wo) ∧
    DestroyStep geometry layout True (first wo) (cid 4) (cid 5) ty left
      ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) destroyedWriteonly :=
  ⟨take_rejects_writeonly_ptr rfl,writeonly_destroy_is_legal⟩

/-- Both halves return to one full raw claim after the complete typed lifecycle. -/
theorem complete_responsibility_cycle :
    WellFormed geometry layout rawState ∧ WellFormed geometry layout merged ∧
    Has merged.ledger (cid 9) (.storage full) ∧
    TotalFootprint geometry merged.ledger = TotalFootprint geometry rawState.ledger ∧
    merged.flat.semantic.usedIncarnations = restarted.flat.semantic.usedIncarnations := by
  refine ⟨raw_state_wellFormed,merged_wellFormed,?_,?_,rfl⟩
  · simp [Has,merged,mergedLedger,mergeCandidate,mergeExtent,mergeRange,left,right,full,
      Extent.left,Extent.right,Range.left,Range.right]
  · exact merged_wellFormed.accounting.coverage.trans raw_state_wellFormed.accounting.coverage.symm

end
end NewLang.F1.Occupancy.Counterexample
