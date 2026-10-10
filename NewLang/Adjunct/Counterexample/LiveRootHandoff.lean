import NewLang.Adjunct.LiveRootHandoff

/-! Concrete original-five experiments for Issue #47. Packet current bindings
are a PROPOSED projection. Heap writes and primitive cleanup are actual accepted
FiveRoot relations; the two layers are not a proved source refinement. -/
namespace NewLang.Adjunct.LiveRootHandoff.Counterexample
open F0 FiveRoot
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

abbrev W := FiveRoot.Counterexample.world
abbrev K := FiveRoot.original W
abbrev heap0 := BComposition.Counterexample.start
abbrev heapDetached := BComposition.Counterexample.detached
abbrev heapAdopted := BComposition.Counterexample.adoptedGraph

def four : Four := ⟨K .src,K .a,K .b,K .c⟩
def initial : Frame := fun b => match b with
  | .donorA => some (.four four)
  | .receiverRoot => some (.ticket (K .dst))
  | _ => none
def splitFrame := detachPost initial four
def openFrame := openPost splitFrame (detachBody four)
def entered := enterPost openFrame (K .dst) (K .b)
def returned := returnPost entered (K .dst) (K .b)

theorem actual_projection_steps :
    Detach initial four ∧ Open splitFrame (detachBody four) ∧
    Enter openFrame (K .dst) (K .b) ∧ Return entered (K .dst) (K .b) := by
  exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩

theorem all_stages_conserve_original_five :
    inventory splitFrame = inventory initial ∧ inventory openFrame = inventory initial ∧
    inventory entered = inventory initial ∧ inventory returned = inventory initial := by
  have h := actual_projection_steps
  have a := detach_conserves h.1
  have b := (open_conserves h.2.1).trans a
  have c := (enter_conserves h.2.2.1).trans b
  exact ⟨a,b,c,(return_conserves h.2.2.2).trans c⟩

/-- Nonduplication is calculated from the five ORIGINAL grants, not a free
singleton-ledger invariant required as a theorem premise. All roles reuse K. -/
theorem each_original_once (i : Site) : (inventory initial).count (K i) = 1 := by
  cases i <;> decide
theorem each_original_once_at_return (i : Site) : (inventory returned).count (K i) = 1 := by
  rw [all_stages_conserve_original_five.2.2.2]; exact each_original_once i

theorem named_return_has_same_dst_and_B :
    returned .treeB = some (.two ⟨K .dst,K .b⟩) ∧
    returned .donor = some (.three ⟨K .src,K .a,K .c⟩) ∧
    returned .donorA = none ∧ returned .receiverRoot = none ∧
    returned .detached = none ∧ returned .result = none ∧
    returned .formalRoot = none ∧ returned .formalChild = none :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem donor_has_no_B_at_return : ¬ LocalCanEnd heapAdopted returned .donor .b := by
  rintro ⟨v,k,available,member,matchK,_⟩
  have veq : v = .three ⟨K .src,K .a,K .c⟩ := Option.some.inj available.symm
  subst v
  have keq : k = K .b := matchK.1
  subst k
  change K .b ∈ ({K .src,K .a,K .c} : Multiset Ticket) at member
  exact (by decide : K .b ∉ ({K .src,K .a,K .c} : Multiset Ticket)) member

theorem old_bindings_have_no_local_release :
    ¬ LocalCanEnd heapAdopted returned .donorA .b ∧
    ¬ LocalCanEnd heapAdopted returned .detached .b ∧
    ¬ LocalCanEnd heapAdopted returned .formalChild .b :=
  ⟨consumed_binding_cannot_end rfl,consumed_binding_cannot_end rfl,consumed_binding_cannot_end rfl⟩

theorem all_five_matched_before_and_after (i : Site) :
    Matched heap0 i (K i) ∧ Matched heapAdopted i (K i) := by
  cases i <;> exact ⟨⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩⟩

/-- Authentic D-specific field refs and all four plus two checked Change/Reset
steps remain the accepted F43 witnesses; no authority is derived from a link. -/
theorem heap_change_endpoints_and_representative_checks :
    Replace (withLoans heap0 {.a}) .a .next
      (FiveRoot.Counterexample.writeRef heap0 .a .next)
      (some (FiveRoot.Counterexample.locator .c)) (FiveRoot.Counterexample.plan 7) ∧
    Replace (withLoans heapDetached {.dst}) .dst .child
      (FiveRoot.Counterexample.writeRef heapDetached .dst .child)
      (some (FiveRoot.Counterexample.locator .b)) (FiveRoot.Counterexample.plan 11) ∧
    FiveRoot.WellFormed heapDetached ∧ FiveRoot.WellFormed heapAdopted :=
  ⟨BComposition.Counterexample.unlinkA_checked,BComposition.Counterexample.linkDst_checked,
    BComposition.Counterexample.detached_wellFormed,BComposition.Counterexample.adoptedGraph_wellFormed⟩

/-- Correct original release order #2,#4,#1, then #3,#5. This starts from the
constructed adoptedGraph, not a new toy heap or the old F43 donor order. -/
def afterA := cleanupPost heapAdopted .a
def afterC := cleanupPost afterA .c
def donorDone := cleanupPost afterC .src
def afterB := cleanupPost donorDone .b
def done := cleanupPost afterB .dst
def afterDonor : Frame := put returned .donor none
/-- Complete terminal destructure, not a nonCopy partial field extraction. -/
def terminalEntered : Frame :=
  put (put (put afterDonor .treeB none) .formalRoot (some (.ticket (K .dst))))
    .formalChild (some (.ticket (K .b)))
def terminalAfterB : Frame := put terminalEntered .formalChild none
def terminalDone : Frame := put terminalAfterB .formalRoot none

private theorem ready {s i} (wf : FiveRoot.WellFormed s)
    (typed : s.cell i = some ⟨.typed,true,0⟩)
    (loans : s.loans = ∅) (deps : s.dependencies = ∅) (known : s.unknownAlias = false) :
    Cleanup s i (s.origin i) (s.origin i) (FiveRoot.full (s.origin i)) := by
  apply cleanup_available wf ⟨_,typed,rfl⟩
  exact ⟨known,by simp [loans],by simp [deps]⟩

theorem finish_A : Cleanup heapAdopted .a (K .a) (K .a) (FiveRoot.full (K .a)) :=
  ready BComposition.Counterexample.adoptedGraph_wellFormed rfl rfl rfl rfl
theorem afterA_wellFormed : FiveRoot.WellFormed afterA := cleanup_preserves_wellFormed finish_A
theorem finish_C : Cleanup afterA .c (K .c) (K .c) (FiveRoot.full (K .c)) :=
  ready afterA_wellFormed rfl rfl rfl rfl
theorem afterC_wellFormed : FiveRoot.WellFormed afterC := cleanup_preserves_wellFormed finish_C
theorem finish_src : Cleanup afterC .src (K .src) (K .src) (FiveRoot.full (K .src)) :=
  ready afterC_wellFormed rfl rfl rfl rfl
theorem donorDone_wellFormed : FiveRoot.WellFormed donorDone := cleanup_preserves_wellFormed finish_src
theorem finish_B : Cleanup donorDone .b (K .b) (K .b) (FiveRoot.full (K .b)) :=
  ready donorDone_wellFormed rfl rfl rfl rfl
theorem afterB_wellFormed : FiveRoot.WellFormed afterB := cleanup_preserves_wellFormed finish_B
theorem finish_dst : Cleanup afterB .dst (K .dst) (K .dst) (FiveRoot.full (K .dst)) :=
  ready afterB_wellFormed rfl rfl rfl rfl
theorem done_wellFormed : FiveRoot.WellFormed done := cleanup_preserves_wellFormed finish_dst

theorem exact_donor_then_receiver_trace :
    FiveRoot.Counterexample.ActualCleanup heapAdopted [.a,.c,.src,.b,.dst] :=
  .cons finish_A (.cons finish_C (.cons finish_src (.cons finish_B (.cons finish_dst (.nil _)))))

theorem after_A_only_TreeTwo_locally_can_end_B_dst :
    donorDone.cell .a = some ⟨.released,false,1⟩ ∧
    LocalCanEnd donorDone afterDonor .treeB .b ∧ LocalCanEnd donorDone afterDonor .treeB .dst := by
  refine ⟨rfl,?_,?_⟩
  · exact ⟨_,K .b,rfl,by simp [Value.tickets],⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,finish_B.endRoot⟩
  · exact ⟨_,K .dst,rfl,by simp [Value.tickets],⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,
      (ready donorDone_wellFormed (i := .dst) rfl rfl rfl rfl).endRoot⟩

theorem terminal_affine_disposition :
    inventory afterDonor = {K .dst,K .b} ∧
    inventory terminalEntered = {K .dst,K .b} ∧
    inventory terminalAfterB = {K .dst} ∧ inventory terminalDone = ∅ ∧
    terminalEntered .treeB = none ∧ terminalDone .formalRoot = none ∧
    terminalDone .formalChild = none := by
  refine ⟨?_,?_,?_,?_,rfl,rfl,rfl⟩
  all_goals simp [inventory,bindings,afterDonor,terminalEntered,terminalAfterB,terminalDone,
    returned,entered,openFrame,splitFrame,initial,returnPost,enterPost,openPost,detachPost,
    put,Value.tickets,detachBody,four]

theorem terminal_each_formal_matched_at_use :
    LocalCanEnd donorDone terminalEntered .formalChild .b ∧
    LocalCanEnd afterB terminalAfterB .formalRoot .dst ∧
    ¬ LocalCanEnd afterB terminalAfterB .formalChild .b ∧
    ¬ LocalCanEnd done terminalDone .formalRoot .dst :=
  ⟨⟨_,K .b,rfl,by simp [Value.tickets],⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,finish_B.endRoot⟩,
    ⟨_,K .dst,rfl,by simp [Value.tickets],⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,finish_dst.endRoot⟩,
    consumed_binding_cannot_end rfl,consumed_binding_cannot_end rfl⟩

theorem original_full_raw_B_dst_recovered :
    (erasePost (endPost donorDone .b) .b).claim .b = some (.storage (FiveRoot.full (K .b))) ∧
    (erasePost (endPost afterB .dst) .dst).claim .dst = some (.storage (FiveRoot.full (K .dst))) ∧
    (K .b).region = (heap0.origin .b).region ∧ (K .dst).region = (heap0.origin .dst).region :=
  ⟨rfl,rfl,rfl,rfl⟩
theorem exact_five_frees_no_remint :
    FiveRoot.Counterexample.freeCount donorDone = 3 ∧ FiveRoot.Counterexample.freeCount done = 5 ∧
    ∀ i : Site, done.cell i = some ⟨.released,false,1⟩ ∧ done.origin i = heap0.origin i ∧
      done.owners i = [] ∧ done.claim i = none := by
  refine ⟨rfl,rfl,?_⟩; intro i; cases i <;> exact ⟨rfl,rfl,rfl,rfl⟩

theorem primitive_B_double_release_rejected (a : Ticket) (raw : F1.Occupancy.Extent) :
    ¬ CanRelease afterB .b a raw := double_release_rejected finish_B

/-- The OLD global predicate still admits B cleanup even though a particular
donor binding is consumed. It cannot serve as source-local release authority. -/
theorem global_canEnd_is_not_local_availability :
    CanEnd heapAdopted .b (K .b) ∧ ¬ LocalCanEnd heapAdopted returned .donorA .b :=
  ⟨(ready BComposition.Counterexample.adoptedGraph_wellFormed (i := .b) rfl rfl rfl rfl).endRoot,
    consumed_binding_cannot_end rfl⟩

def allocationPackets (n : Fin 6) : List Ticket := [K .src,K .a,K .b,K .c,K .dst].take n.val
theorem failures_no_unseen_packet (n : Fin 6) (i : Site) :
    K i ∈ allocationPackets n ↔ i.code < n.val := by
  rcases n with ⟨n,bound⟩
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst n <;> cases i <;> decide +revert
theorem allocation_failure_exact_frees (n : Fin 6) :
    (allocationPackets n).length = n.val ∧
    FiveRoot.Counterexample.ActualCleanup (FiveRoot.Counterexample.outcome n)
      (FiveRoot.Counterexample.cleanupOrder n) ∧
    FiveRoot.Counterexample.freeCount (FiveRoot.Counterexample.finished n) = n.val := by
  refine ⟨?_,FiveRoot.Counterexample.all_six_outcomes_are_actual n,
    FiveRoot.Counterexample.exact_zero_to_five_frees n⟩
  rcases n with ⟨n,bound⟩
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases cases with h|h|h|h|h|h <;> subst n <;> rfl

/-- Corrupting a current frame without a typed refund loses two originals.
This is an omitted-exit countermodel for an adapter accepting arbitrary exits,
not an execution edge of M's closed straight-line body. -/
def boolOnlyPost : Frame := put (put entered .formalRoot none) .formalChild none
theorem bool_only_postconsume_error_loses_both :
    (inventory boolOnlyPost).count (K .b) = 0 ∧
    (inventory boolOnlyPost).count (K .dst) = 0 ∧
    inventory boolOnlyPost ≠ inventory entered := by
  refine ⟨by decide,by decide,?_⟩
  intro equal
  have b := congrArg (Multiset.count (K .b)) equal
  have one : (inventory entered).count (K .b) = 1 := by
    rw [all_stages_conserve_original_five.2.2.1]; exact each_original_once .b
  rw [one] at b; change 0 = 1 at b; omega

def copyOnly : Frame := put returned .treeB (some (.ticket (K .dst)))
theorem copy_only_receiver_does_not_have_B : ¬ LocalCanEnd heapAdopted copyOnly .treeB .b := by
  rintro ⟨v,k,available,member,matched,_⟩
  have veq : v = .ticket (K .dst) := Option.some.inj available.symm
  subst v
  have keq : k = K .b := matched.1
  subst k
  change K .b ∈ ({K .dst} : Multiset Ticket) at member
  exact (by decide : K .b ∉ ({K .dst} : Multiset Ticket)) member

/-- H0 keeps B safely in an unrelated caller packet while Tree B retains only
dst. Unlike the lost-B control, all five originals are still accounted. -/
def unrelatedCallerPacket : Frame :=
  put (put openFrame .receiverRoot none) .treeB (some (.ticket (K .dst)))
theorem H0_conserves_inventory_but_fails_receiver_ownership :
    inventory unrelatedCallerPacket = inventory initial ∧
    LocalCanEnd heapAdopted unrelatedCallerPacket .detached .b ∧
    ¬ LocalCanEnd heapAdopted unrelatedCallerPacket .treeB .b := by
  refine ⟨?_,?_,?_⟩
  · rw [← all_stages_conserve_original_five.2.1]
    apply Multiset.ext.mpr; intro k
    simp [inventory,bindings,unrelatedCallerPacket,put,openFrame,splitFrame,initial,
      openPost,detachPost,detachBody,Value.tickets,four,Multiset.count_cons,
      Multiset.count_singleton,add_comm,add_left_comm,add_assoc]
  · exact ⟨.ticket (K .b),K .b,rfl,by simp [Value.tickets],
      (all_five_matched_before_and_after .b).2,
      (ready BComposition.Counterexample.adoptedGraph_wellFormed (i := .b) rfl rfl rfl rfl).endRoot⟩
  · rintro ⟨v,k,available,member,matched,can⟩
    exact copy_only_receiver_does_not_have_B ⟨v,k,available,member,matched,can⟩

def wrongWorld : Ticket := {K .b with world := ⟨W.index+1⟩}
def samePtrWrongR : Ticket := {K .b with region := (K .c).region}
theorem wrong_world_and_same_ptr_wrong_region_rejected :
    wrongWorld.ptr = (K .b).ptr ∧ samePtrWrongR.ptr = (K .b).ptr ∧
    ¬ Matched heapAdopted .b wrongWorld ∧ ¬ Matched heapAdopted .b samePtrWrongR :=
  ⟨rfl,rfl,matched_wrong_world_rejected (by decide),matched_wrong_region_rejected (by decide)⟩

theorem B_absent_from_TreeTwo_is_not_completed :
    (inventory copyOnly).count (K .b) = 0 ∧ inventory copyOnly ≠ inventory initial := by
  refine ⟨by decide,?_⟩
  intro equal
  have b := congrArg (Multiset.count (K .b)) equal
  change 0 = 1 at b; omega

/-- A correct p/D field-write proof does NOT inspect the unused Allocation
constituent. Exact A/R matching at attach return needs its own provenance
transport proof; it cannot be inferred from successful writes alone. -/
def wrongAllocation : Ticket := {K .b with allocation := (K .c).allocation}
def forgedBRef : FieldRef :=
  ⟨⟨wrongAllocation.world,wrongAllocation.ptr,wrongAllocation.domain,⟨true,true⟩⟩,.prev,projection .prev⟩
theorem field_body_does_not_check_allocation_constituent :
    wrongAllocation.ptr = (K .b).ptr ∧ wrongAllocation.domain = (K .b).domain ∧
    wrongAllocation.allocation ≠ (K .b).allocation ∧
    Replace (withLoans BComposition.Counterexample.linkDst {.b}) .b .prev forgedBRef
      (some (FiveRoot.Counterexample.locator .b)) (FiveRoot.Counterexample.plan 12) ∧
    ¬ Matched heapAdopted .b wrongAllocation :=
  ⟨rfl,rfl,by decide,BComposition.Counterexample.adoptedGraph_checked,
    matched_wrong_allocation_rejected (by decide)⟩

def duplicateFrame : Frame := put openFrame .treeB (some (.ticket (K .b)))
theorem local_entry_alone_does_not_prove_unique_custody :
    Enter duplicateFrame (K .dst) (K .b) ∧ (inventory duplicateFrame).count (K .b) = 2 :=
  ⟨⟨rfl,rfl,rfl,rfl⟩,by decide⟩

theorem entry_projection_alone_does_not_check_heap_loan :
    Enter openFrame (K .dst) (K .b) ∧
    Matched (withLoans heapDetached {.b}) .b (K .b) ∧
    ¬ CanEnd (withLoans heapDetached {.b}) .b (K .b) := by
  refine ⟨actual_projection_steps.2.2.1,⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,?_⟩
  intro endB; exact endB.2.2.2.1 (by simp [withLoans])

/-- Closed straight-line body at the ORIGINAL fixture. Affine operations and
matched inputs are candidate assumptions; both write judgments are independently
checked accepted witnesses. This does not check proposed source borrowing. -/
def ClosedAttach (s : Frame) (r k : Ticket) (post : Frame) : Prop :=
  Enter s r k ∧ s .treeB = none ∧ Matched heapDetached .dst r ∧ Matched heapDetached .b k ∧
  post = returnPost (enterPost s r k) r k
theorem closed_attach_constructive_totality {s r k}
    (entry : Enter s r k) (empty : s .treeB = none)
    (receiver : Matched heapDetached .dst r) (child : Matched heapDetached .b k) :
    ∃ post, ClosedAttach s r k post ∧ inventory post = inventory s ∧
      FiveRoot.WellFormed heapAdopted := by
  refine ⟨returnPost (enterPost s r k) r k,⟨entry,empty,receiver,child,rfl⟩,?_,
    BComposition.Counterexample.adoptedGraph_wellFormed⟩
  have ret : Return (enterPost s r k) r k := by
    refine ⟨?_,?_,?_⟩ <;> simp [enterPost,put,empty]
  exact (return_conserves ret).trans (enter_conserves entry)
theorem actual_closed_attach : ClosedAttach openFrame (K .dst) (K .b) returned :=
  ⟨actual_projection_steps.2.2.1,rfl,⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,⟨rfl,rfl,⟨⟨.typed,true,0⟩,rfl,rfl⟩⟩,rfl⟩
theorem closed_attach_has_no_boolean_error_edge :
    ¬ ClosedAttach openFrame (K .dst) (K .b) boolOnlyPost := by
  intro call
  have same := congrFun call.2.2.2.2 Binding.treeB
  have absent : boolOnlyPost .treeB = none := rfl
  have present : returnPost (enterPost openFrame (K .dst) (K .b)) (K .dst) (K .b) .treeB =
      some (.two ⟨K .dst,K .b⟩) := rfl
  rw [absent,present] at same
  cases same

private def refusalStart (detached : Bool) := if detached then heapDetached else heap0
private def refusalB (detached : Bool) := cleanupPost (refusalStart detached) .b
private def refusalA (detached : Bool) := cleanupPost (refusalB detached) .a
private def refusalC (detached : Bool) := cleanupPost (refusalA detached) .c
private def refusalSrc (detached : Bool) := cleanupPost (refusalC detached) .src
private def refusalDone (detached : Bool) := cleanupPost (refusalSrc detached) .dst
private theorem refusalStart_wf (d : Bool) : FiveRoot.WellFormed (refusalStart d) := by
  cases d
  · exact FiveRoot.Counterexample.wired6_wellFormed
  · exact BComposition.Counterexample.detached_wellFormed
private theorem refusal_B (d : Bool) : Cleanup (refusalStart d) .b (K .b) (K .b) (FiveRoot.full (K .b)) := by
  cases d <;> exact ready (refusalStart_wf _) rfl rfl rfl rfl
private theorem refusalB_wf (d : Bool) : FiveRoot.WellFormed (refusalB d) := cleanup_preserves_wellFormed (refusal_B d)
private theorem refusal_A (d : Bool) : Cleanup (refusalB d) .a (K .a) (K .a) (FiveRoot.full (K .a)) := by
  cases d <;> exact ready (refusalB_wf _) rfl rfl rfl rfl
private theorem refusalA_wf (d : Bool) : FiveRoot.WellFormed (refusalA d) := cleanup_preserves_wellFormed (refusal_A d)
private theorem refusal_C (d : Bool) : Cleanup (refusalA d) .c (K .c) (K .c) (FiveRoot.full (K .c)) := by
  cases d <;> exact ready (refusalA_wf _) rfl rfl rfl rfl
private theorem refusalC_wf (d : Bool) : FiveRoot.WellFormed (refusalC d) := cleanup_preserves_wellFormed (refusal_C d)
private theorem refusal_src (d : Bool) : Cleanup (refusalC d) .src (K .src) (K .src) (FiveRoot.full (K .src)) := by
  cases d <;> exact ready (refusalC_wf _) rfl rfl rfl rfl
private theorem refusalSrc_wf (d : Bool) : FiveRoot.WellFormed (refusalSrc d) := cleanup_preserves_wellFormed (refusal_src d)
private theorem refusal_dst (d : Bool) : Cleanup (refusalSrc d) .dst (K .dst) (K .dst) (FiveRoot.full (K .dst)) := by
  cases d <;> exact ready (refusalSrc_wf _) rfl rfl rfl rfl
private theorem refusal_actual (d : Bool) :
    FiveRoot.Counterexample.ActualCleanup (refusalStart d) [.b,.a,.c,.src,.dst] := by
  cases d <;> exact .cons (refusal_B _) (.cons (refusal_A _) (.cons (refusal_C _)
    (.cons (refusal_src _) (.cons (refusal_dst _) (.nil _)))))

theorem pre_detach_and_detached_refusal_exact_cleanup :
    FiveRoot.Counterexample.ActualCleanup heap0 [.b,.a,.c,.src,.dst] ∧
    FiveRoot.Counterexample.ActualCleanup heapDetached [.b,.a,.c,.src,.dst] ∧
    FiveRoot.Counterexample.freeCount (refusalDone false) = 5 ∧
    FiveRoot.Counterexample.freeCount (refusalDone true) = 5 :=
  ⟨refusal_actual false,refusal_actual true,rfl,rfl⟩

end
end NewLang.Adjunct.LiveRootHandoff.Counterexample
