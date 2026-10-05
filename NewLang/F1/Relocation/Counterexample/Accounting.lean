import NewLang.F1.Relocation.Counterexample.Model

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing
open Occupancy.Counterexample (geometry layout ty cid region rw ro wo)
noncomputable section

def stageLedger (k : Case) (started : Bool) : Occupancy.Ledger :=
  if started then ledgerCandidate (beforeLedger k) (move k) else beforeLedger k
def stageLocation (started : Bool) := if started then destination else source
def stageExtent (k : Case) (started : Bool) := if started then dstExtent k else srcExtent
def stageRootClaim (started : Bool) := if started then cid 4 else cid 0

def stagePhysical (k : Case) (a : Access) (started : Bool) : PhysicalState :=
  ⟨world k a,fun l => if l = stageLocation started then some ((stageExtent k started).placement geometry) else none⟩

private theorem source_handle_inactive_after (k : Case) : cid 0 ∉ (stageLedger k true).active := by
  cases k <;> simp [stageLedger,ledgerCandidate,beforeLedger,move,inputIds,frameIds,cid]

private theorem stage_root_present (k : Case) (started : Bool) :
    Occupancy.Has (stageLedger k started) (stageRootClaim started)
      (.root ty (stageLocation started) (stageExtent k started)) := by
  cases started <;> simp [Occupancy.Has,stageLedger,stageRootClaim,stageLocation,stageExtent,ledgerCandidate,beforeLedger,move]

private theorem stage_root_only (k : Case) (started : Bool) {id t l e}
    (active : id ∈ (stageLedger k started).active) (eq : (stageLedger k started).claim id = .root t l e) :
    id = stageRootClaim started ∧ t = ty ∧ l = stageLocation started ∧ e = stageExtent k started := by
  cases started
  · by_cases same : id = cid 0
    · subst id; simpa [stageLedger,beforeLedger,stageRootClaim,stageLocation,stageExtent,eq_comm] using eq
    · by_cases i1 : id = cid 1 <;> by_cases i5 : id = cid 5 <;> simp only [cid] at same i1 i5 <;> simp [stageLedger,beforeLedger,same,i1,i5,cid] at eq
  · have old : id ≠ cid 0 := fun same => source_handle_inactive_after k (same ▸ active)
    by_cases same : id = cid 4
    · subst id; simpa [stageLedger,ledgerCandidate,move,stageRootClaim,stageLocation,stageExtent,eq_comm] using eq
    · cases k <;> by_cases out : id = cid 3 <;> by_cases i1 : id = cid 1 <;> by_cases i5 : id = cid 5 <;>
        simp only [cid] at same out old i1 i5
      all_goals simp [stageLedger,ledgerCandidate,move,same,out,beforeLedger,old,i1,i5,cid] at eq

private def stageIds : Case → Bool → Finset Occupancy.ClaimId
  | .overlap,false => {cid 0,cid 1,cid 2}
  | .overlap,true => {cid 4,cid 2,cid 3}
  | .disjoint,false => {cid 0,cid 1}
  | .disjoint,true => {cid 4,cid 3}
  | .different,false => {cid 0,cid 1,cid 2,cid 5}
  | .different,true => {cid 4,cid 2,cid 5,cid 3}
  | .equal,false => {cid 0,cid 2}
  | .equal,true => {cid 4,cid 2}

private theorem stage_active (k : Case) (b : Bool) : (stageLedger k b).active = stageIds k b := by
  cases k <;> cases b <;> decide
private theorem stage_scope (k : Case) (b : Bool) : (stageLedger k b).scope = regions k := by
  cases b <;> rfl

private theorem stage_checks (k : Case) (started : Bool) : ∀ id ∈ (stageLedger k started).active,
    ((stageLedger k started).claim id).extent.region ∈ regions k ∧
    0 < ((stageLedger k started).claim id).extent.range.length ∧
    ((stageLedger k started).claim id).extent.Fits geometry ∧
    ((stageLedger k started).claim id).Typed layout := by
  intro id active
  rw [stage_active] at active
  cases k <;> cases started
  all_goals simp only [stageIds,Finset.mem_insert,Finset.mem_singleton] at active
  case overlap.false => rcases active with rfl|rfl|rfl <;> (simp [stageLedger,beforeLedger,cid,srcExtent,inputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case overlap.true => rcases active with rfl|rfl|rfl <;> (simp [stageLedger,ledgerCandidate,beforeLedger,move,cid,srcExtent,dstExtent,inputExtent,outputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case disjoint.false => rcases active with rfl|rfl <;> (simp [stageLedger,beforeLedger,cid,srcExtent,dstExtent,inputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case disjoint.true => rcases active with rfl|rfl <;> (simp [stageLedger,ledgerCandidate,beforeLedger,move,cid,srcExtent,dstExtent,inputExtent,outputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case different.false => rcases active with rfl|rfl|rfl|rfl <;> (simp [stageLedger,beforeLedger,cid,srcExtent,dstExtent,inputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case different.true => rcases active with rfl|rfl|rfl|rfl <;> (simp [stageLedger,ledgerCandidate,beforeLedger,move,cid,srcExtent,dstExtent,inputExtent,outputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case equal.false => rcases active with rfl|rfl <;> (simp [stageLedger,beforeLedger,cid,srcExtent,dstExtent,inputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )
  case equal.true => rcases active with rfl|rfl <;> (simp [stageLedger,ledgerCandidate,beforeLedger,move,cid,srcExtent,dstExtent,inputExtent,outputExtent,frameExtent,regions,region,geometry,layout,ty,Occupancy.Extent.Fits,Occupancy.Range.finish,Occupancy.Claim.Typed,Occupancy.Claim.extent] )

private theorem stage_no_overlap (k : Case) (started : Bool) : Occupancy.NoOverlap geometry (stageLedger k started) := by
  intro i ia j ja different
  rw [stage_active] at ia ja
  cases k <;> cases started
  all_goals simp only [stageIds,Finset.mem_insert,Finset.mem_singleton] at ia ja
  case overlap.false => rcases ia with rfl|rfl|rfl <;> rcases ja with rfl|rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case overlap.true => rcases ia with rfl|rfl|rfl <;> rcases ja with rfl|rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case disjoint.false => rcases ia with rfl|rfl <;> rcases ja with rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case disjoint.true => rcases ia with rfl|rfl <;> rcases ja with rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case different.false => rcases ia with rfl|rfl|rfl|rfl <;> rcases ja with rfl|rfl|rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case different.true => rcases ia with rfl|rfl|rfl|rfl <;> rcases ja with rfl|rfl|rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case equal.false => rcases ia with rfl|rfl <;> rcases ja with rfl|rfl <;> first | exact False.elim (different rfl) | decide
  case equal.true => rcases ia with rfl|rfl <;> rcases ja with rfl|rfl <;> first | exact False.elim (different rfl) | decide

/-- Both complete endpoints, including same-region overlap and different regions,
satisfy the same reviewed F1.4 accounting, without post-WF assumptions. -/
theorem stage_accounting (k : Case) (a : Access) (started : Bool) :
    Occupancy.Accounting geometry layout (fun l => l = stageLocation started)
      (stagePhysical k a started) (stageLedger k started) := by
  constructor
  · constructor
    · intro r; rfl
    · intro r rl q ql different
      cases k <;> simp [stagePhysical,world,regions] at rl ql
      case overlap => exact False.elim (different (rl.trans ql.symm))
      case disjoint => exact False.elim (different (rl.trans ql.symm))
      case equal => exact False.elim (different (rl.trans ql.symm))
      case different =>
        rcases rl with rfl|rfl <;> rcases ql with rfl|rfl
        all_goals first | exact False.elim (different rfl) | (dsimp [stagePhysical,world]; decide)
    · intro r member; simpa [stage_scope,stagePhysical,world] using member
    · intro id active; simpa [stage_scope] using (stage_checks k started id active).1
    · intro id active; exact (stage_checks k started id active).2.1
    · intro id active; exact (stage_checks k started id active).2.2.1
    · intro id active; exact (stage_checks k started id active).2.2.2
    · intro l; constructor
      · intro eq; subst l
        exact ⟨stageRootClaim started,(stage_root_present k started).1,ty,stageExtent k started,(stage_root_present k started).2⟩
      · rintro ⟨id,active,t,e,eq⟩; exact (stage_root_only k started active eq).2.2.1
    · intro l pl; constructor
      · intro placed
        by_cases loc : l = stageLocation started
        · have pe : (stageExtent k started).placement geometry = pl := by simpa [stagePhysical,loc] using placed
          exact ⟨stageRootClaim started,(stage_root_present k started).1,ty,stageExtent k started,
            by simpa [loc] using (stage_root_present k started).2,pe⟩
        · simp [stagePhysical,loc] at placed
      · rintro ⟨id,active,t,e,eq,pe⟩
        rcases stage_root_only k started active eq with ⟨_,_,loc,extent⟩
        simpa [stagePhysical,loc,extent] using congrArg some pe
  · exact stage_no_overlap k started
  · cases k <;> cases started <;> dsimp [Occupancy.ExpectedFootprint,stagePhysical,world] <;> decide

private theorem before_accounting (k : Case) (a : Access) (deps ext : Finset Conditional.Fact) :
    Occupancy.Accounting geometry layout (fun l => l ∈ (before k a deps ext).accounted.base.semantic.liveRoots)
      (before k a deps ext).accounted.base.physical (before k a deps ext).accounted.ledger := by
  simpa [before,semantic,stagePhysical,stageLocation,stageExtent,stageLedger] using stage_accounting k a false

private theorem after_accounting (k : Case) (a : Access) (deps ext : Finset Conditional.Fact) :
    Occupancy.Accounting geometry layout (fun l => l ∈ (after k a deps ext).accounted.base.semantic.liveRoots)
      (after k a deps ext).accounted.base.physical (after k a deps ext).accounted.ledger := by
  have physical : (after k a deps ext).accounted.base.physical = stagePhysical k a true := by
    simp [after,candidate,physicalCandidate,before,stagePhysical,stageLocation,stageExtent,move,startPlacement,endPlacement]
    funext l
    by_cases src : l = source
    · subst l; simp [source,destination]
    · by_cases dst : l = destination
      · subst l; simp [destination]
      · simp only [ite_eq_right src,ite_eq_right dst]
  rw [physical]
  simpa [after,candidate,semanticCandidate,before,semantic,move,source,destination,stageLocation,stageLedger] using stage_accounting k a true

private theorem owned_present (k : Case) (s : State) (started : Bool)
    (data : s.data = annotation k) (ledger : s.accounted.ledger = stageLedger k started) :
    ∀ p, Conditional.Survives s.accounted.base.semantic p → ∀ id ∈ (s.data p).ownedClaims,
      id ∈ s.accounted.ledger.active ∧ (s.accounted.ledger.claim id).valueOwned = true := by
  intro p _ id member
  by_cases package : p = pkg
  · subst p; by_cases disjoint : k = .disjoint
    · simp [data,annotation,disjoint] at member
    · have eq : id = cid 2 := by simpa [data,annotation,disjoint] using member
      subst id; cases k <;> cases started
      all_goals first | exact False.elim (disjoint rfl) |
        simp [ledger,stageLedger,ledgerCandidate,beforeLedger,move,inputIds,frameIds,Occupancy.Claim.valueOwned,cid]
  · simp [data,annotation,package] at member

private theorem owned_unique (k : Case) (s : State) (data : s.data = annotation k) :
    ∀ p q, Conditional.Survives s.accounted.base.semantic p → Conditional.Survives s.accounted.base.semantic q →
      p ≠ q → Disjoint (s.data p).ownedClaims (s.data q).ownedClaims := by
  intro p q _ _ different
  by_cases pp : p = pkg <;> by_cases qp : q = pkg
  · exact False.elim (different (pp.trans qp.symm))
  all_goals simp [data,annotation,pp,qp]

theorem independent_before_wellFormed (k : Case) (a : Access) : WellFormed geometry layout (before k a ∅ ∅) :=
  ⟨⟨before_invariant ∅ ∅,independent_dependencies _ rfl,before_accounting k a ∅ ∅⟩,
    owned_present k _ false rfl rfl,owned_unique k _ rfl⟩

theorem independent_after_wellFormed (k : Case) (a : Access) : WellFormed geometry layout (after k a ∅ ∅) :=
  ⟨⟨after_invariant k a ∅ ∅,independent_dependencies _ rfl,after_accounting k a ∅ ∅⟩,
    owned_present k _ true rfl rfl,owned_unique k _ rfl⟩

end
end NewLang.F1.Relocation.Counterexample
