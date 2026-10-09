import NewLang.Adjunct.BComposition
import NewLang.Adjunct.Counterexample.Custody

namespace NewLang.Adjunct.BComposition.Counterexample
open F0 F1.Backing F1.Occupancy FiveRoot
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

abbrev start := FiveRoot.Counterexample.wired6
abbrev world := FiveRoot.Counterexample.world
abbrev locator := FiveRoot.Counterexample.locator
abbrev plan := FiveRoot.Counterexample.plan
abbrev writeRef := FiveRoot.Counterexample.writeRef

/-- Source-shaped field experiment only; this operation NEVER transfers B owners. -/
def write (s : FiveRoot.State) (i : Site) (f : Field)
    (v : Option (LiveTail.WorldId × PtrToken)) (n : Nat) : FiveRoot.State :=
  withLoans (changePost (withLoans s {i}) i f v (plan n)) ∅

private theorem write_preserves_memory (s : FiveRoot.State) (i : Site) (f : Field) (v) (n : Nat) :
    (write s i f v n).origin = s.origin ∧ (write s i f v n).owners = s.owners ∧
    (write s i f v n).cell = s.cell ∧ (write s i f v n).claim = s.claim := ⟨rfl,rfl,rfl,rfl⟩

private theorem checked_write {s i f v n} (wf : FiveRoot.WellFormed s)
    (live : Typed s i) (domain : DomainAlive s i) (permission : s.permission i = ⟨true,true⟩)
    (incoming : ∀ ptr, v = some ptr → Issued s ptr) (fresh : ChangeFresh s (plan n))
    (guard : ChangeGuard s i f) :
    Replace (withLoans s {i}) i f (writeRef s i f) v (plan n) := by
  refine ⟨withLoans_wellFormed wf _,?_,rfl,incoming,fresh,guard⟩
  refine ⟨⟨rfl,rfl,rfl,live,domain,by simp [withLoans],?_⟩,rfl,rfl⟩
  simp [AccessLe,FiveRoot.Counterexample.writeRef,withLoans,permission]

private theorem write_wellFormed {s i f v n}
    (step : Replace (withLoans s {i}) i f (writeRef s i f) v (plan n)) :
    FiveRoot.WellFormed (write s i f v n) :=
  withLoans_wellFormed (change_preserves_wellFormed step) _

def unlinkA := write start .a .next (some (locator .c)) 7
theorem unlinkA_checked : Replace (withLoans start {.a}) .a .next
    (writeRef start .a .next) (some (locator .c)) (plan 7) := by
  apply checked_write FiveRoot.Counterexample.wired6_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.c,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem unlinkA_wellFormed : FiveRoot.WellFormed unlinkA := write_wellFormed unlinkA_checked

def unlinkC := write unlinkA .c .prev (some (locator .a)) 8
theorem unlinkC_checked : Replace (withLoans unlinkA {.c}) .c .prev
    (writeRef unlinkA .c .prev) (some (locator .a)) (plan 8) := by
  apply checked_write unlinkA_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem unlinkC_wellFormed : FiveRoot.WellFormed unlinkC := write_wellFormed unlinkC_checked

def clearPrev := write unlinkC .b .prev none 9
theorem clearPrev_checked : Replace (withLoans unlinkC {.b}) .b .prev
    (writeRef unlinkC .b .prev) none (plan 9) := by
  apply checked_write unlinkC_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem clearPrev_wellFormed : FiveRoot.WellFormed clearPrev := write_wellFormed clearPrev_checked

def detached := write clearPrev .b .next none 10
theorem detached_checked : Replace (withLoans clearPrev {.b}) .b .next
    (writeRef clearPrev .b .next) none (plan 10) := by
  apply checked_write clearPrev_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem detached_wellFormed : FiveRoot.WellFormed detached := write_wellFormed detached_checked

def linkDst := write detached .dst .child (some (locator .b)) 11
theorem linkDst_checked : Replace (withLoans detached {.dst}) .dst .child
    (writeRef detached .dst .child) (some (locator .b)) (plan 11) := by
  apply checked_write detached_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem linkDst_wellFormed : FiveRoot.WellFormed linkDst := write_wellFormed linkDst_checked

def adoptedGraph := write linkDst .b .prev (some (locator .b)) 12
theorem adoptedGraph_checked : Replace (withLoans linkDst {.b}) .b .prev
    (writeRef linkDst .b .prev) (some (locator .b)) (plan 12) := by
  apply checked_write linkDst_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem adoptedGraph_wellFormed : FiveRoot.WellFormed adoptedGraph := write_wellFormed adoptedGraph_checked

theorem four_detach_relations :
    (detached.link .a .next).payload = some (locator .c) ∧
    (detached.link .c .prev).payload = some (locator .a) ∧
    (detached.link .b .prev).payload = none ∧ (detached.link .b .next).payload = none := ⟨rfl,rfl,rfl,rfl⟩

theorem two_adoption_relations :
    (adoptedGraph.link .dst .child).payload = some (locator .b) ∧
    (adoptedGraph.link .b .prev).payload = some (locator .b) := ⟨rfl,rfl⟩

theorem all_link_updates_preserve_five_originals :
    adoptedGraph.origin = start.origin ∧ adoptedGraph.owners = start.owners ∧
    adoptedGraph.cell = start.cell ∧ adoptedGraph.claim = start.claim := by
  have h1 := write_preserves_memory start .a .next (some (locator .c)) 7
  have h2 := write_preserves_memory unlinkA .c .prev (some (locator .a)) 8
  have h3 := write_preserves_memory unlinkC .b .prev none 9
  have h4 := write_preserves_memory clearPrev .b .next none 10
  have h5 := write_preserves_memory detached .dst .child (some (locator .b)) 11
  have h6 := write_preserves_memory linkDst .b .prev (some (locator .b)) 12
  exact ⟨h6.1.trans (h5.1.trans (h4.1.trans (h3.1.trans (h2.1.trans h1.1)))),
    h6.2.1.trans (h5.2.1.trans (h4.2.1.trans (h3.2.1.trans (h2.2.1.trans h1.2.1)))),
    h6.2.2.1.trans (h5.2.2.1.trans (h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans h1.2.2.1)))),
    h6.2.2.2.trans (h5.2.2.2.trans (h4.2.2.2.trans (h3.2.2.2.trans (h2.2.2.2.trans h1.2.2.2))))⟩

theorem graph_adoption_does_not_move_B_responsibility :
    adoptedGraph.owners .b = [.allocation (original world .b),.domain (original world .b)] ∧
    adoptedGraph.owners .dst = [.allocation (original world .dst),.domain (original world .dst)] := ⟨rfl,rfl⟩

/-- A concrete naive donor-local cut leaves original B live but loses its ledger. -/
def naiveCut : FiveRoot.State :=
  {adoptedGraph with owners := fun i => if i = .b then [] else adoptedGraph.owners i}
theorem naive_cut_preserves_original_live_B :
    Typed naiveCut .b ∧ naiveCut.origin .b = original world .b ∧ naiveCut.owners .b = [] :=
  ⟨⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl,rfl⟩
theorem naive_donor_cut_is_not_an_adapter : ¬ FiveRoot.WellFormed naiveCut :=
  deleting_live_B_owners_breaks_five_invariant naive_cut_preserves_original_live_B.1 rfl

/-- Copy ptr retained in dst cannot repair a missing Allocation/Domain carrier. -/
theorem copy_link_cannot_repair_B_owner :
    (naiveCut.link .dst .child).payload = some (locator .b) ∧ ¬ FiveRoot.WellFormed naiveCut :=
  ⟨rfl,naive_donor_cut_is_not_an_adapter⟩

/-- External actor labels are only projections of the EXISTING custody support. -/
theorem simultaneous_donor_recipient_impossible {g s}
    (wf : Custody.WellFormed g s) (live : s.heap.memory.tail.phase = .typed) :
    ¬ (Custodian.donor ∈ support s ∧ Custodian.recipient ∈ support s) := by
  rcases rich_live_has_one_custodian wf live with ⟨h,only,_⟩
  rw [only]; rintro ⟨a,b⟩
  have aa : Custodian.donor = h := Finset.mem_singleton.mp a
  have bb : Custodian.recipient = h := Finset.mem_singleton.mp b
  have impossible := aa.trans bb.symm; cases impossible

private theorem ready_cleanup {s i} (wf : FiveRoot.WellFormed s)
    (cell : s.cell i = some ⟨.typed,true,0⟩) (loans : s.loans = ∅)
    (deps : s.dependencies = ∅) (known : s.unknownAlias = false) :
    Cleanup s i (s.origin i) (s.origin i) (full (s.origin i)) := by
  apply cleanup_available wf ⟨_,cell,rfl⟩
  exact ⟨known,by simp [loans],by simp [deps]⟩

def donor1 := cleanupPost adoptedGraph .src
theorem donor1_step : Cleanup adoptedGraph .src (adoptedGraph.origin .src)
    (adoptedGraph.origin .src) (full (adoptedGraph.origin .src)) :=
  ready_cleanup adoptedGraph_wellFormed rfl rfl rfl rfl
theorem donor1_wellFormed : FiveRoot.WellFormed donor1 := cleanup_preserves_wellFormed donor1_step

def donor2 := cleanupPost donor1 .a
theorem donor2_step : Cleanup donor1 .a (donor1.origin .a) (donor1.origin .a) (full (donor1.origin .a)) :=
  ready_cleanup donor1_wellFormed rfl rfl rfl rfl
theorem donor2_wellFormed : FiveRoot.WellFormed donor2 := cleanup_preserves_wellFormed donor2_step

def donorDone := cleanupPost donor2 .c
theorem donorDone_step : Cleanup donor2 .c (donor2.origin .c) (donor2.origin .c) (full (donor2.origin .c)) :=
  ready_cleanup donor2_wellFormed rfl rfl rfl rfl
theorem donorDone_wellFormed : FiveRoot.WellFormed donorDone := cleanup_preserves_wellFormed donorDone_step

theorem donor_cleanup_keeps_original_B_dst_live :
    donorDone.cell .a = some ⟨.released,false,1⟩ ∧
    donorDone.cell .b = some ⟨.typed,true,0⟩ ∧ donorDone.cell .dst = some ⟨.typed,true,0⟩ ∧
    donorDone.origin .b = original world .b ∧ donorDone.origin .dst = original world .dst :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- After only donor cleanup, B must remain accounted and still needs release.
This state is not a normal zero-obligation exit and must not be called complete. -/
theorem skipped_B_release_leaves_nonCopy_residue :
    donorDone.owners .b ≠ [] ∧ donorDone.claim .b ≠ none ∧
    FiveRoot.Counterexample.freeCount donorDone = 3 := by
  refine ⟨?_,?_,rfl⟩ <;> decide

theorem B_cannot_be_ended_under_scoped_loan :
    ¬ CanEnd (withLoans adoptedGraph {.b}) .b (original world .b) := by
  intro step; exact step.2.2.2.1 (by simp [withLoans])

theorem crossed_B_domain_rejected : ¬ CanEnd adoptedGraph .b (original world .c) := by
  intro step
  have same : original world .c = original world .b := endRoot_requires_original_domain adoptedGraph_wellFormed step
  have eq := original_domain_injective world (congrArg FiveRoot.Origin.domain same)
  cases eq

theorem old_A_next_occurrence_cannot_follow_new_link :
    ¬ FactLive unlinkA (.occurrence ⟨102⟩) :=
  changed_old_occurrence_not_live unlinkA_checked rfl

/-- Omitting A.next rewiring is a policy error, not memory-unsafety. -/
def wrongPolicy := write start .c .prev (some (locator .a)) 7
theorem wrongPolicy_checked : Replace (withLoans start {.c}) .c .prev
    (writeRef start .c .prev) (some (locator .a)) (plan 7) := by
  apply checked_write FiveRoot.Counterexample.wired6_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wrong_graph_policy_is_still_memory_wellFormed :
    FiveRoot.WellFormed wrongPolicy ∧ (wrongPolicy.link .a .next).payload ≠ some (locator .c) :=
  ⟨write_wellFormed wrongPolicy_checked,by decide⟩

/-- Coarse two-root projection of the ACTUAL donorDone cells; original head=A,
tail=B. All ordinary ownership/dependency invariants hold, but headLive does not. -/
def projectionRoot (i : Site) (fact : ValueFactId) : KnownCall.Root :=
  ⟨(original world i).ptr.location,parentPlace i,(original world i).ptr.incarnation,fact,
    ⟨i.code+1⟩,(original world i).domain,full (original world i),∅,true⟩
def projectedRoots : KnownCall.Context :=
  ⟨projectionRoot .a (plan 7).parent,projectionRoot .b (plan 12).parent,⟨0⟩,1⟩
def projectedMemory : KnownCall.State where
  head := ⟨.released,false,1⟩
  tail := ⟨.typed,true,0⟩
  carrier := fun role => match role with
    | .headAllocation | .headDomain => none
    | .tailAllocation => some (original world .b).allocation
    | .tailDomain => some (original world .b).domainBinding
  usedBindings := {(original world .b).allocation,(original world .b).domainBinding}
  externalDependencies := ∅
  blockers := ∅
  issuedPtrs := {(original world .b).ptr}
  readableRegions := {(original world .b).region}
  platformReady := true

theorem projection_has_exact_actual_cells :
    donorDone.cell .a = some projectedMemory.head ∧ donorDone.cell .b = some projectedMemory.tail ∧
    projectedRoots.tail.location = (donorDone.origin .b).ptr.location ∧
    projectedRoots.tail.incarnation = (donorDone.origin .b).ptr.incarnation ∧
    projectedRoots.tail.extent.region = (donorDone.origin .b).region ∧
    projectedRoots.tail.domain = (donorDone.origin .b).domain := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem projected_context_valid : KnownCall.ContextValid FiveRoot.Counterexample.geometry projectedRoots := by
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
  · exact FiveRoot.Counterexample.original_full_extents_disjoint (by decide : Site.a ≠ .b)

theorem projected_memory_wellFormed : KnownCall.WellFormed projectedRoots projectedMemory := by
  constructor
  · intro i; cases i <;> simp [projectedMemory,KnownCall.allocationRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [projectedMemory,KnownCall.domainRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [projectedMemory,KnownCall.State.cell]
  · intro i; cases i <;> simp [projectedMemory,KnownCall.State.cell]
  · intro i; cases i <;> simp [projectedMemory,KnownCall.State.cell]
  · intro i; cases i <;> rfl
  · intro role b eq
    cases role <;> simp [projectedMemory] at eq
    · subst b; simp [projectedMemory]
    · subst b; simp [projectedMemory]
  · intro r q b rb qb
    cases r <;> cases q <;> simp [projectedMemory] at rb qb ⊢ <;>
      first | rfl | (subst b; contradiction)
  · constructor
    · intro i _ fact mem; cases i <;> simp [projectedRoots,projectionRoot,KnownCall.Context.root] at mem
    · simp [projectedMemory]

def projectedArgs : KnownCall.Arguments :=
  ⟨⟨(original world .b).ptr,⟨(original world .b).region,⟨true,true⟩⟩⟩,
    (original world .b).region,(original world .b).allocation,(original world .b).domain,
    (original world .b).domainBinding⟩

theorem exact_B_identity_and_carriers_survive :
    projectedMemory.tail.phase = .typed ∧
    projectedArgs.ptr.token = ⟨projectedRoots.tail.location,projectedRoots.tail.incarnation⟩ ∧
    projectedArgs.allocationRegion = projectedRoots.tail.extent.region ∧
    projectedMemory.carrier .tailAllocation = some projectedArgs.allocationBinding ∧
    projectedArgs.domain = projectedRoots.tail.domain ∧
    projectedMemory.carrier .tailDomain = some projectedArgs.domainBinding ∧
    projectedMemory.tail.releases = 0 := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem delayed_B_call_has_concrete_head_blocker (a d : F2.BindingId) (post : KnownCall.State) :
    ¬ KnownCall.Call FiveRoot.Counterexample.geometry projectedRoots projectedMemory projectedArgs a d post :=
  legacy_call_rejects_released_head rfl

theorem independent_B_primitive_cleanup_still_available :
    Cleanup donorDone .b (donorDone.origin .b) (donorDone.origin .b) (full (donorDone.origin .b)) :=
  ready_cleanup donorDone_wellFormed rfl rfl rfl rfl

/-- No manufactured transfer: keep the existing exact pre-transfer failures. -/
theorem pre_transfer_failure_worlds_remain_guarded (n : Fin 6) :
    FiveRoot.Counterexample.ActualCleanup (FiveRoot.Counterexample.outcome n)
      (FiveRoot.Counterexample.cleanupOrder n) ∧
    FiveRoot.Counterexample.freeCount (FiveRoot.Counterexample.finished n) = n.val :=
  ⟨FiveRoot.Counterexample.all_six_outcomes_are_actual n,FiveRoot.Counterexample.exact_zero_to_five_frees n⟩

/-- A refused already-checked source application changes no heap data. This is
not an actual call certificate for the five-root frame. -/
theorem refusal_is_a_rich_heap_frame (s : Custody.State) :
    (Custody.refuse s).heap = s.heap ∧ (Custody.refuse s).packet = s.packet ∧
    (Custody.refuse s).holders = s.holders := ⟨rfl,rfl,rfl⟩


/-- Every remaining entry obligation is concretely satisfied; this implication
only packages them and does not supply the false head-live premise. -/
theorem projected_entry_if_head_live
    (live : projectedMemory.head.phase = .typed) :
    KnownCall.RequiredAtEntry projectedRoots projectedMemory projectedArgs := by
  constructor
  · exact live
  all_goals first | rfl | decide

/-- Reuse a REAL accepted old two-root call to expose its caller-owned sink.
This witness is intentionally not claimed to be the five-root original B. -/
theorem old_recipient_has_caller_owned_sink :
    ∃ g body s r p post, Custody.RecipientCall g body s r p post ∧
      post.container = s.container ∧ post.container.callerOwned = true := by
  refine ⟨_,_,_,_,_,_, Custody.Counterexample.actual_recipient_call,?_⟩
  exact accepted_recipient_preserves_caller_owned_destination
    Custody.Counterexample.actual_recipient_call

end
end NewLang.Adjunct.BComposition.Counterexample
