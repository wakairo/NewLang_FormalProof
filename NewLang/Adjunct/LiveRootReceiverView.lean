import NewLang.Adjunct.Counterexample.LiveRootHandoff

/-! Issue #47: a NEW independently checked dst/B known-call VIEW of the actual
post-adopt five-world cells, after A/C/src release. This does not mutate/rebase
Custody.approved, or certify TreeTwo source evaluation/whole argument transfer.
The accepted KnownCall slice models exact terminal identity/accounting but is
not the complete F1 structured-value/occupancy refinement. -/
namespace NewLang.Adjunct.LiveRootHandoff.ReceiverView
open F0 F1.Backing F1.Occupancy FiveRoot
open LiveRootHandoff.Counterexample
noncomputable section

def root (i : Site) : KnownCall.Root :=
  ⟨(K i).ptr.location,parentPlace i,(K i).ptr.incarnation,donorDone.parentFact i,
    ⟨i.code+1⟩,(K i).domain,FiveRoot.full (K i),∅,true⟩
def roots : KnownCall.Context := ⟨root .dst,root .b,⟨0⟩,1⟩
def before : KnownCall.State where
  head := ⟨.typed,true,0⟩
  tail := ⟨.typed,true,0⟩
  carrier := fun role => match role with
    | .headAllocation => some (K .dst).allocation
    | .headDomain => some (K .dst).domainBinding
    | .tailAllocation => some (K .b).allocation
    | .tailDomain => some (K .b).domainBinding
  usedBindings := {(K .dst).allocation,(K .dst).domainBinding,(K .b).allocation,(K .b).domainBinding}
  externalDependencies := ∅
  blockers := ∅
  issuedPtrs := {(K .b).ptr,(K .dst).ptr}
  readableRegions := {(K .b).region,(K .dst).region}
  platformReady := true
def args : KnownCall.Arguments :=
  ⟨⟨(K .b).ptr,⟨(K .b).region,⟨true,true⟩⟩⟩,
    (K .b).region,(K .b).allocation,(K .b).domain,(K .b).domainBinding⟩
def post : KnownCall.State := KnownCall.callPost before ⟨100⟩ ⟨101⟩

theorem exact_actual_original_cells :
    donorDone.cell .a = some ⟨.released,false,1⟩ ∧
    donorDone.cell .dst = some before.head ∧ donorDone.cell .b = some before.tail ∧
    roots.tail.location = (donorDone.origin .b).ptr.location ∧
    roots.tail.incarnation = (donorDone.origin .b).ptr.incarnation ∧
    roots.tail.domain = (donorDone.origin .b).domain ∧
    roots.tail.extent = FiveRoot.full (donorDone.origin .b) ∧
    roots.head.extent = FiveRoot.full (donorDone.origin .dst) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem new_context_valid : KnownCall.ContextValid FiveRoot.Counterexample.geometry roots := by
  constructor
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · exact FiveRoot.Counterexample.original_full_extents_disjoint (by decide : Site.dst ≠ .b)

theorem before_wellFormed : KnownCall.WellFormed roots before := by
  constructor
  · intro i; cases i <;> simp [before,KnownCall.allocationRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [before,KnownCall.domainRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [before,KnownCall.State.cell]
  · intro i; cases i <;> simp [before,KnownCall.State.cell]
  · intro i; cases i <;> simp [before,KnownCall.State.cell]
  · intro i; cases i <;> rfl
  · intro role b eq
    cases role <;> simp [before] at eq <;> subst b <;> simp [before]
  · intro r q b rb qb
    cases r <;> cases q <;> simp [before] at rb qb ⊢ <;>
      first | rfl | (subst b; contradiction)
  · constructor
    · intro i _ f member; cases i <;> simp [roots,root,KnownCall.Context.root] at member
    · simp [before]

theorem new_entry_proved : KnownCall.RequiredAtEntry roots before args := by
  constructor
  all_goals first | rfl | decide
theorem actual_B_known_call_after_A_dead :
    KnownCall.Call FiveRoot.Counterexample.geometry roots before args ⟨100⟩ ⟨101⟩ post := by
  refine ⟨new_context_valid,before_wellFormed,new_entry_proved,?_,?_,rfl⟩
  · constructor <;> decide
  · intro f member; simp [roots,root,before] at member

theorem post_wellFormed : KnownCall.WellFormed roots post :=
  KnownCall.known_call_preserves_wellFormed actual_B_known_call_after_A_dead
theorem exact_actual_post_cells :
    afterB.cell .dst = some post.head ∧ afterB.cell .b = some post.tail := ⟨rfl,rfl⟩
theorem terminal_recovers_same_full_B :
    KnownCall.responsibility roots (KnownCall.eraseSlot (KnownCall.endRoot
      (KnownCall.transfer before ⟨100⟩ ⟨101⟩))) .tail =
        some (.storage (FiveRoot.full (K .b))) ∧
    roots.tail.extent.range = ⟨0,FiveRoot.Counterexample.geometry.capacity (K .b).region⟩ ∧
    post.tail.releases = 1 ∧ post.carrier .tailAllocation = none ∧ post.carrier .tailDomain = none :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem new_call_no_callee_packet_residue :
    ∀ role, post.carrier role ≠ some ⟨100⟩ ∧ post.carrier role ≠ some ⟨101⟩ :=
  KnownCall.parameter_bindings_are_consumed_at_return actual_B_known_call_after_A_dead
theorem new_call_B_cannot_double_release (b : F2.BindingId) (raw : Extent) :
    ¬ KnownCall.CanDeallocate roots post b raw :=
  KnownCall.known_call_cannot_double_release actual_B_known_call_after_A_dead b raw

/-- The old A/B call still MUST fail; this file does not weaken it. -/
theorem old_A_head_still_blocks (a d : F2.BindingId) (p : KnownCall.State) :
    ¬ KnownCall.Call FiveRoot.Counterexample.geometry BComposition.Counterexample.projectedRoots
      BComposition.Counterexample.projectedMemory BComposition.Counterexample.projectedArgs a d p :=
  BComposition.Counterexample.delayed_B_call_has_concrete_head_blocker a d p

/-- After B's release, simply swapping that old two-root call view does NOT
give the dst terminal. A separately checked per-root finish_root interface is
still necessary, although accepted FiveRoot primitive finish_dst exists. -/
def dstRoots : KnownCall.Context := ⟨roots.tail,roots.head,⟨0⟩,1⟩
def dstBefore : KnownCall.State :=
  {post with
    head := post.tail
    tail := post.head
    carrier := fun role => match role with
      | .headAllocation => post.carrier .tailAllocation
      | .headDomain => post.carrier .tailDomain
      | .tailAllocation => post.carrier .headAllocation
      | .tailDomain => post.carrier .headDomain}
theorem second_old_call_is_not_finish_two (as : KnownCall.Arguments) (a d : F2.BindingId)
    (p : KnownCall.State) : ¬ KnownCall.Call FiveRoot.Counterexample.geometry dstRoots dstBefore as a d p :=
  BComposition.legacy_call_rejects_released_head rfl

end
end NewLang.Adjunct.LiveRootHandoff.ReceiverView
