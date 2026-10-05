import NewLang.F1.Occupancy.Counterexample.Overlap

namespace NewLang.F1.Occupancy.Counterexample
open F0 Backing
noncomputable section

-- Wrong-range endpoints below remain fully well-formed; the operation relation,
-- rather than an unrelated malformed state, rejects the changed responsibility.
private def mirrorPhysical (a : Access) (active : Bool) : PhysicalState :=
  ⟨world a,fun l => if active ∧ l = ⟨0⟩ then some (right.placement geometry) else none⟩

private theorem mirror_shape (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId) (c : Claim)
    (scope : s.scope = {region 0}) (ids : s.active = {id,cid 20}) (different : id ≠ cid 20)
    (lc : s.claim id = c) (rc : s.claim (cid 20) = .storage left)
    (extent : c.extent = right) (typed : c.Typed layout)
    (rootClaim : ∀ t l e, c = .root t l e ↔ active = true ∧ t = ty ∧ l = ⟨0⟩ ∧ e = right) :
    AccountingShape geometry layout (FlatLive (semantic active n loose history)) (mirrorPhysical a active) s := by
  have classify : ∀ i ∈ s.active, i = id ∨ i = cid 20 := by
    intro i member; simpa [ids] using member
  have lcExtent : (s.claim id).extent = right := by rw [lc,extent]
  constructor
  · intro r; rfl
  · intro r rl q ql neq
    exact False.elim (neq ((Finset.mem_singleton.mp rl).trans (Finset.mem_singleton.mp ql).symm))
  · intro r member; simpa [scope,mirrorPhysical,world] using member
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent,scope]; exact Finset.mem_singleton_self _
    · rw [rc,scope]; exact Finset.mem_singleton.mpr (by rfl)
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent]; decide
    · rw [rc]; decide
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent]; change 4 ≤ 4; decide
    · rw [rc]; change 2 ≤ 4; decide
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lc]; exact typed
    · simp [rc,Claim.Typed]
  · intro l; constructor
    · rintro ⟨r,h⟩; rcases live_iff.mp h with ⟨act,le,_⟩
      exact ⟨id,by simp [ids],ty,right,lc.trans ((rootClaim ty l right).mpr ⟨act,rfl,le,rfl⟩)⟩
    · rintro ⟨i,member,t,e,claim⟩
      rcases classify i member with rfl|rfl
      · rw [lc] at claim
        rcases (rootClaim t l e).mp claim with ⟨act,_,le,_⟩
        exact ⟨root n,live_iff.mpr ⟨act,le,rfl⟩⟩
      · simp [rc] at claim
  · intro l pl; constructor
    · intro placed
      have act : active = true := by cases active <;> simp [mirrorPhysical] at placed ⊢
      have loc : l = ⟨0⟩ := by by_cases eq : l = ⟨0⟩ <;> simp [mirrorPhysical,act,eq] at placed ⊢
      have pe : right.placement geometry = pl := by simpa [mirrorPhysical,act,loc] using placed
      exact ⟨id,by simp [ids],ty,right,lc.trans ((rootClaim ty l right).mpr ⟨act,rfl,loc,rfl⟩),pe⟩
    · rintro ⟨i,member,t,e,claim,pe⟩
      rcases classify i member with rfl|rfl
      · rw [lc] at claim
        rcases (rootClaim t l e).mp claim with ⟨act,_,le,ee⟩
        simpa [mirrorPhysical,act,le,ee] using congrArg some pe
      · simp [rc] at claim

private theorem mirror_accounting (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId) (c : Claim)
    (scope : s.scope = {region 0}) (ids : s.active = {id,cid 20}) (different : id ≠ cid 20)
    (lc : s.claim id = c) (rc : s.claim (cid 20) = .storage left)
    (extent : c.extent = right) (typed : c.Typed layout)
    (rootClaim : ∀ t l e, c = .root t l e ↔ active = true ∧ t = ty ∧ l = ⟨0⟩ ∧ e = right) :
    Accounting geometry layout (FlatLive (semantic active n loose history)) (mirrorPhysical a active) s := by
  refine ⟨mirror_shape a active n loose history s id c scope ids different lc rc extent typed rootClaim,?_,?_⟩
  · intro i ia j ja neq
    have ic : i = id ∨ i = cid 20 := by simpa [ids] using ia
    have jc : j = id ∨ j = cid 20 := by simpa [ids] using ja
    rcases ic with rfl|rfl <;> rcases jc with rfl|rfl
    · exact False.elim (neq rfl)
    · rw [lc,rc,extent,Claim.extent]
      exact (split_extents_disjoint geometry full 2).symm
    · rw [lc,rc,extent,Claim.extent]
      exact split_extents_disjoint geometry full 2
    · exact False.elim (neq rfl)
  · have partition : right.footprint geometry ∪ left.footprint geometry = full.footprint geometry :=
      by rw [Finset.union_comm]; exact split_extents_exact_union geometry (by decide)
    have total : TotalFootprint geometry s = right.footprint geometry ∪ left.footprint geometry := by
      have rightEq : (s.claim id).extent.footprint geometry = right.footprint geometry := by rw [lc,extent]
      have leftEq : (s.claim (cid 20)).extent.footprint geometry = left.footprint geometry := by rw [rc]; rfl
      simp [TotalFootprint,ids,rightEq,leftEq]
    rw [total]
    simpa [ExpectedFootprint,scope,mirrorPhysical,world,Extent.footprint,full,Range.positions,Range.finish] using partition

private def wrongLedger (id : ClaimId) (c : Claim) : Ledger :=
  ⟨{region 0},{id,cid 20},fun i => if i = id then c else .storage left⟩
private def wrongInitialized : State :=
  ⟨⟨(first rw).flat.semantic,mirrorPhysical rw true⟩,wrongLedger (cid 4) (.root ty ⟨0⟩ right)⟩
private def wrongTaken : State :=
  ⟨(taken rw).flat,wrongLedger (cid 5) (.slot ty right)⟩
private def wrongErased : State :=
  ⟨ended.flat,wrongLedger (cid 8) (.storage right)⟩

private theorem wrong_initialized_wf : WellFormed geometry layout wrongInitialized := by
  refine ⟨(first_wellFormed rw).toWellFormed,?_⟩
  apply mirror_accounting rw true 1 ∅ {1} _ (cid 4) (.root ty ⟨0⟩ right)
  all_goals simp [wrongInitialized,wrongLedger,cid,Claim.extent,Claim.Typed,ty,layout,
    right,full,Extent.right,Range.right,eq_comm]

private theorem wrong_taken_wf : WellFormed geometry layout wrongTaken := by
  refine ⟨(taken_wellFormed rw).toWellFormed,?_⟩
  apply mirror_accounting rw false 1 {⟨0⟩} {1} _ (cid 5) (.slot ty right)
  all_goals simp [wrongTaken,wrongLedger,cid,Claim.extent,Claim.Typed,ty,layout,
    right,full,Extent.right,Range.right,eq_comm]

private theorem wrong_erased_wf : WellFormed geometry layout wrongErased := by
  refine ⟨ended_wellFormed.toWellFormed,?_⟩
  apply mirror_accounting rw false 2 ∅ {1,2} _ (cid 8) (.storage right)
  all_goals simp [wrongErased,wrongLedger,cid,Claim.extent,Claim.Typed,ty,
    right,full,Extent.right,Range.right,eq_comm]

theorem initialize_wrong_range_control_has_valid_endpoints :
    WellFormed geometry layout (slotState rw) ∧ WellFormed geometry layout wrongInitialized ∧
    wrongInitialized.flat.semantic = (first rw).flat.semantic ∧
    ¬ RawInitialize geometry sites True True (slotState rw) (cid 3) (cid 4) ty left
      ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩ (evidence rw) wrongInitialized := by
  refine ⟨slot_state_wellFormed rw,wrong_initialized_wf,rfl,?_⟩
  intro raw
  have placed := (initialize_consumes_slot_and_preserves_exact_responsibility raw).2.2
  have same : right.placement geometry = left.placement geometry := Option.some.inj placed
  exact (show right.placement geometry ≠ left.placement geometry from by decide) same

theorem take_wrong_slot_control_has_valid_endpoints :
    WellFormed geometry layout (first rw) ∧ WellFormed geometry layout wrongTaken ∧
    wrongTaken.flat = (taken rw).flat ∧
    ¬ RawTake True (first rw) (cid 4) (cid 5) ty left ⟨0⟩ (root 1) ⟨0⟩ (ptr rw) wrongTaken := by
  refine ⟨first_wellFormed rw,wrong_taken_wf,rfl,?_⟩
  intro raw
  have correct := (take_consumes_root_and_returns_same_slot raw).2.1.2
  have same : right = left := Claim.slot.inj correct |>.2
  exact (show right ≠ left from by decide) same

theorem erase_slot_wrong_range_control_has_valid_endpoints :
    WellFormed geometry layout ended ∧ WellFormed geometry layout wrongErased ∧
    wrongErased.flat = ended.flat ∧
    ¬ RawEraseSlot endLedger (cid 7) (cid 8) ty left wrongErased.ledger := by
  refine ⟨ended_wellFormed,wrong_erased_wf,rfl,?_⟩
  intro raw
  have correct := (erase_slot_consumes_empty_exact_range raw).2.2
  have same : right = left := Claim.storage.inj correct
  exact (show right ≠ left from by decide) same

private def lostDestroy : Ledger :=
  {restartLedger with active := restartLedger.active.erase (cid 6)}
private def lostState : State := ⟨ended.flat,lostDestroy⟩

theorem destroy_lost_responsibility_control :
    F0.WellFormed lostState.flat.semantic ∧
    AccountingShape geometry layout (FlatLive lostState.flat.semantic) lostState.flat.physical lostDestroy ∧
    NoOverlap geometry lostDestroy ∧
    (⟨0⟩ : AbstractByteId) ∈ ExpectedFootprint lostState.flat.physical lostDestroy ∧
    (⟨0⟩ : AbstractByteId) ∉ TotalFootprint geometry lostDestroy ∧
    ¬ RawDestroy True restarted (cid 6) (cid 7) ty left ⟨0⟩ (root 2) ⟨0⟩ secondPtr lostState := by
  refine ⟨ended_wellFormed.toWellFormed,?_,?_,?_,?_,?_⟩
  · have correct := ended_wellFormed.accounting.toAccountingShape
    have only : lostDestroy.active = {cid 20} := by
      simp [lostDestroy,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,
        splitLedger,splitCandidate,rawLedger,cid]
    have data : lostDestroy.claim (cid 20) = .storage right := by
      simp [lostDestroy,restartLedger,takenLedger,liveLedger,slotLedger,consumeOne,
        splitLedger,splitCandidate,rawLedger,cid,right]
    constructor
    · exact correct.geometry
    · exact correct.regions
    · exact correct.scopeLive
    · intro i active; have eq : i = cid 20 := by simpa [only] using active
      subst i; change region 0 ∈ ({region 0} : Finset BackingRegionId); simp
    · intro i active; have eq : i = cid 20 := by simpa [only] using active
      subst i; rw [data]; decide
    · intro i active; have eq : i = cid 20 := by simpa [only] using active
      subst i; rw [data]; change 4 ≤ 4; decide
    · intro i active; have eq : i = cid 20 := by simpa [only] using active
      subst i; rw [data]; trivial
    · intro l; constructor
      · rintro ⟨r,h⟩; simp [lostState,ended,flat,semantic] at h
      · rintro ⟨i,active,t,e,h⟩; have eq : i = cid 20 := by simpa [only] using active
        subst i; rw [data] at h; cases h
    · intro l pl; constructor
      · intro h; simp [lostState,ended,flat,physical] at h
      · rintro ⟨i,active,t,e,h,_⟩; have eq : i = cid 20 := by simpa [only] using active
        subst i; rw [data] at h; cases h
  · intro i ia j ja neq
    have ie : i = cid 20 := by simpa [lostDestroy,restartLedger,takenLedger,liveLedger,slotLedger,
      consumeOne,splitLedger,splitCandidate,rawLedger,cid] using ia
    have je : j = cid 20 := by simpa [lostDestroy,restartLedger,takenLedger,liveLedger,slotLedger,
      consumeOne,splitLedger,splitCandidate,rawLedger,cid] using ja
    exact False.elim (neq (ie.trans je.symm))
  · change (⟨0⟩ : AbstractByteId) ∈ (world rw).bytes (region 0); decide
  · change (⟨0⟩ : AbstractByteId) ∉ right.footprint geometry; decide
  · intro raw
    have returned := (destroy_consumes_root_and_returns_same_slot raw).2.1.1
    simp [lostState,lostDestroy,restartLedger,takenLedger,liveLedger,slotLedger,
      consumeOne,splitLedger,splitCandidate,rawLedger,cid] at returned

private def largerErased : Ledger := consumeOne endLedger (cid 7) (cid 8) (.storage full)
private def differentErased : Ledger := consumeOne endLedger (cid 7) (cid 8) (.storage ⟨region 1,left.range⟩)

theorem erase_slot_larger_or_different_region_controls :
    ¬ RawEraseSlot endLedger (cid 7) (cid 8) ty left largerErased ∧
    ¬ RawEraseSlot endLedger (cid 7) (cid 8) ty left differentErased := by
  constructor
  · intro raw
    have correct := (erase_slot_consumes_empty_exact_range raw).2.2
    have same : full = left := Claim.storage.inj (by simpa [largerErased,consumeOne] using correct)
    exact (show full ≠ left from by decide) same
  · intro raw
    have correct := (erase_slot_consumes_empty_exact_range raw).2.2
    have same : Extent.mk (region 1) left.range = left := Claim.storage.inj (by simpa [differentErased,consumeOne] using correct)
    exact (show Extent.mk (region 1) left.range ≠ left from by decide) same

theorem representation_change_is_possible_without_new_authority :
    RepresentationOnlyStep ⟨slotState rw,0⟩ ⟨slotState rw,99⟩ ∧
    (⟨slotState rw,0⟩ : RepresentationObservation).opaqueContents ≠
      (⟨slotState rw,99⟩ : RepresentationObservation).opaqueContents := ⟨rfl,by decide⟩

end
end NewLang.F1.Occupancy.Counterexample
