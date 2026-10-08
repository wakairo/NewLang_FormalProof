import NewLang.Adjunct.KnownCallProofs

namespace NewLang.Adjunct.KnownCall.Counterexample
open F0 F1.Backing F1.Occupancy
noncomputable section

private def geometry : Geometry where
  capacity := fun _ => 1
  byteAt := fun r n => ⟨r.index * 10 + n⟩
  injective := by
    intro r a b eq
    have same := congrArg AbstractByteId.index eq
    dsimp at same
    omega

private def context (headDeps tailDeps : Finset F0.Fact := ∅) : Context where
  head := ⟨⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨⟨1⟩,⟨0,1⟩⟩,headDeps,true⟩
  tail := ⟨⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨⟨2⟩,⟨0,1⟩⟩,tailDeps,true⟩
  type := ⟨0⟩
  size := 1

private def before (external : Finset F0.Fact := ∅) : State where
  head := ⟨.typed,true,0⟩
  tail := ⟨.typed,true,0⟩
  carrier := fun r => match r with
    | .headAllocation => some ⟨1⟩ | .headDomain => some ⟨2⟩
    | .tailAllocation => some ⟨3⟩ | .tailDomain => some ⟨4⟩
  usedBindings := {⟨1⟩,⟨2⟩,⟨3⟩,⟨4⟩}
  externalDependencies := external
  blockers := ∅
  issuedPtrs := {⟨⟨1⟩,⟨1⟩⟩,⟨⟨2⟩,⟨2⟩⟩}
  readableRegions := {⟨1⟩,⟨2⟩}
  platformReady := true

private def args : Arguments :=
  ⟨⟨⟨⟨2⟩,⟨2⟩⟩,⟨⟨2⟩,⟨true,true⟩⟩⟩,⟨2⟩,⟨3⟩,⟨2⟩,⟨4⟩⟩

private theorem valid (h t : Finset F0.Fact) : ContextValid geometry (context h t) := by
  constructor
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · dsimp [context]; decide
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · dsimp [context]; decide

private theorem entry (h t ext : Finset F0.Fact) : RequiredAtEntry (context h t) (before ext) args := by
  constructor <;> first | rfl | exact Finset.notMem_empty _ | (dsimp [before,args,context]; decide)

private theorem fresh (ext : Finset F0.Fact) : FreshParameters (before ext) ⟨5⟩ ⟨6⟩ := by
  constructor <;> dsimp [before] <;> decide

private theorem invariant (h t ext : Finset F0.Fact)
    (deps : DependenciesValid (context h t) (before ext)) :
    WellFormed (context h t) (before ext) := by
  constructor
  · intro i; cases i <;> simp [before,allocationRole,State.cell]
  · intro i; cases i <;> simp [before,domainRole,State.cell]
  · intro i; cases i <;> simp [before,State.cell]
  · intro i; cases i <;> simp [before,State.cell]
  · intro i; cases i <;> simp [before,State.cell]
  · intro i; cases i <;> rfl
  · intro r b present
    cases r <;> simp [before] at present <;> subst b <;> simp [before]
  · intro r q b rb qb
    cases r <;> cases q <;> simp [before] at rb qb ⊢ <;>
      first | rfl | (subst b; contradiction)
  · exact deps

private theorem noDeps : DependenciesValid (context ∅ ∅) (before ∅) := by
  constructor
  · intro i typed f dep; cases i <;> simp [context,Context.root] at dep
  · simp [before]

/-- Entry is a separately proved relation; not a signature-only permission. -/
theorem matched_entry_is_provable : RequiredAtEntry (context ∅ ∅) (before ∅) args := entry _ _ _

theorem independent_two_root_call_exists :
    Call geometry (context ∅ ∅) (before ∅) args ⟨5⟩ ⟨6⟩ (callPost (before ∅) ⟨5⟩ ⟨6⟩) := by
  refine ⟨valid _ _,invariant _ _ _ noDeps,entry _ _ _,fresh _,?_,rfl⟩
  simp [SurvivorGuard,context,before]

theorem original_head_live_tail_released_once :
    (callPost (before ∅) ⟨5⟩ ⟨6⟩).head.phase = .typed ∧
    (callPost (before ∅) ⟨5⟩ ⟨6⟩).tail.phase = .released ∧
    (callPost (before ∅) ⟨5⟩ ⟨6⟩).tail.releases = 1 := by
  decide

private def wrongPtr : Arguments :=
  {args with ptr := ⟨⟨⟨1⟩,⟨1⟩⟩,⟨⟨1⟩,⟨true,true⟩⟩⟩}
private def wrongAllocation : Arguments :=
  {args with allocationRegion := ⟨1⟩, allocationBinding := ⟨1⟩}
private def wrongDomain : Arguments := {args with domain := ⟨1⟩, domainBinding := ⟨2⟩}

/-- Exactly ptr_h, A_t, D_t; static types are unchanged. -/
theorem head_ptr_tail_owners_rejected : ¬ RequiredAtEntry (context ∅ ∅) (before ∅) wrongPtr :=
  entry_rejects_wrong_ptr (by decide)

/-- Exactly ptr_t, A_h, D_t. -/
theorem tail_ptr_head_allocation_rejected : ¬ RequiredAtEntry (context ∅ ∅) (before ∅) wrongAllocation :=
  entry_rejects_wrong_allocation_region (by decide)

/-- Exactly ptr_t, A_t, D_h. -/
theorem tail_ptr_head_domain_rejected : ¬ RequiredAtEntry (context ∅ ∅) (before ∅) wrongDomain :=
  entry_rejects_wrong_domain (by decide)

/-- A stale incarnation of the right place/region also fails entry. -/
theorem stale_tail_ptr_rejected :
    ¬ RequiredAtEntry (context ∅ ∅) (before ∅)
      {args with ptr := {args.ptr with token := ⟨⟨2⟩,⟨9⟩⟩}} :=
  entry_rejects_wrong_ptr (by decide)

/-- Deliberately broken eager handoff. It changes the caller despite failed entry;
production Call cannot take this path. The rejected call has no transition. -/
theorem unchecked_handoff_before_entry_breaks_rollback :
    ¬ RequiredAtEntry (context ∅ ∅) (before ∅) wrongPtr ∧
    (transfer (before ∅) ⟨5⟩ ⟨6⟩).carrier .tailAllocation = some ⟨5⟩ ∧
    (transfer (before ∅) ⟨5⟩ ⟨6⟩).carrier .tailAllocation ≠ (before ∅).carrier .tailAllocation :=
  ⟨head_ptr_tail_owners_rejected,rfl,by decide⟩

theorem same_region_wrong_carrier_rejected :
    ¬ RequiredAtEntry (context ∅ ∅) (before ∅) {args with allocationBinding := ⟨1⟩} := by
  intro h; have wrong := h.allocation; simp [before] at wrong

theorem typed_occupancy_cannot_be_deallocated : ¬ CanDeallocate (context ∅ ∅) (before ∅) ⟨3⟩ (context ∅ ∅).tail.extent :=
  typed_root_cannot_release rfl

theorem recovered_tail_storage_cannot_release_head_allocation :
    ¬ CanDeallocate (context ∅ ∅) (finalize (eraseSlot (endRoot (transfer (before ∅) ⟨5⟩ ⟨6⟩))))
      ⟨1⟩ (context ∅ ∅).tail.extent := by
  intro h; have wrong := h.2.2.1; simp [before,transfer,finalize,eraseSlot,endRoot] at wrong

theorem double_release_rejected :
    ¬ CanDeallocate (context ∅ ∅) (callPost (before ∅) ⟨5⟩ ⟨6⟩) ⟨5⟩ (context ∅ ∅).tail.extent :=
  known_call_cannot_double_release independent_two_root_call_exists _ _

theorem historical_parameter_binding_reuse_rejected : ¬ FreshParameters (before ∅) ⟨3⟩ ⟨6⟩ := by
  intro h; exact h.allocationFresh (by decide)

theorem ending_scope_conflict_rejected :
    ¬ RequiredAtEntry (context ∅ ∅) {(before ∅) with blockers := {.root ⟨2⟩}} args :=
  entry_rejects_scope_conflict (by decide)

private def tailFact : F0.Fact := .valueFact ⟨2⟩ ⟨2⟩
private def tailDomain : F0.Fact := .domainLive ⟨2⟩

/-- Discarding the tail package atomically may remove its own dependency. -/
theorem old_only_dependency_consumed_by_receiver :
    Call geometry (context ∅ {tailFact,tailDomain}) (before ∅) args ⟨5⟩ ⟨6⟩
      (callPost (before ∅) ⟨5⟩ ⟨6⟩) := by
  have deps : DependenciesValid (context ∅ {tailFact,tailDomain}) (before ∅) := by
    constructor
    · intro i typed f member
      cases i with
      | head => simp [context,Context.root] at member
      | tail =>
        have which : f = tailFact ∨ f = tailDomain := by simpa [context,Context.root] using member
        rcases which with rfl|rfl
        · exact ⟨.tail,rfl,rfl,rfl⟩
        · exact ⟨.tail,rfl,rfl⟩
    · simp [before]
  refine ⟨valid _ _,invariant _ _ _ deps,entry _ _ _,fresh _,?_,rfl⟩
  simp [SurvivorGuard,context,before]

theorem surviving_head_dependency_rejects_receiver :
    ¬ SurvivorGuard (context {tailFact} ∅) (before ∅) := by
  intro h; exact (h tailFact (Or.inl (by simp [context]))).1 rfl

theorem external_current_dependency_rejects_receiver :
    ¬ SurvivorGuard (context ∅ ∅) (before {tailFact}) := by
  intro h; exact (h tailFact (Or.inr (by simp [before]))).1 rfl

theorem external_domain_dependency_rejects_receiver :
    ¬ SurvivorGuard (context ∅ ∅) (before {tailDomain}) := by
  intro h; exact (h tailDomain (Or.inr (by simp [before]))).2 rfl

/-- Removing the guard keeps authority accounting but leaves a dead dependency. -/
theorem unchecked_receiver_breaks_dependency_preservation :
    ¬ DependenciesValid (context {tailFact} ∅) (receiver (before ∅)) := by
  intro h
  have live := h.1 .head rfl tailFact (by simp [context,Context.root])
  rcases live with ⟨i,typed,place,fact⟩
  cases i with
  | head => simp [context,Context.root] at place
  | tail => simp [receiver,deallocate,State.cell] at typed

theorem mismatched_entry_cannot_grant_even_if_handoff_wellFormed :
    ¬ RequiredAtEntry (context ∅ ∅) (before ∅) wrongPtr ∧
    WellFormed (context ∅ ∅) (transfer (before ∅) ⟨5⟩ ⟨6⟩) :=
  ⟨head_ptr_tail_owners_rejected,transfer_preserves_wellFormed (invariant _ _ _ noDeps) (entry _ _ _) (fresh _)⟩

theorem head_dependency_prestate_is_wellFormed : WellFormed (context {tailFact} ∅) (before ∅) := by
  apply invariant
  constructor
  · intro i typed f member
    cases i with
    | head =>
      have same : f = tailFact := by simpa [context,Context.root] using member
      subst f; exact ⟨.tail,rfl,rfl,rfl⟩
    | tail => simp [context,Context.root] at member
  · simp [before]

theorem head_dependency_has_no_call (post : State) :
    ¬ Call geometry (context {tailFact} ∅) (before ∅) args ⟨5⟩ ⟨6⟩ post :=
  surviving_ended_dependency_has_no_call surviving_head_dependency_rejects_receiver

theorem external_dependency_prestate_is_wellFormed :
    WellFormed (context ∅ ∅) (before {tailFact,tailDomain}) := by
  apply invariant
  constructor
  · intro i typed f member; cases i <;> simp [context,Context.root] at member
  · intro f member
    have which : f = tailFact ∨ f = tailDomain := by simpa [before] using member
    rcases which with rfl|rfl
    · exact ⟨.tail,rfl,rfl,rfl⟩
    · exact ⟨.tail,rfl,rfl⟩

theorem external_dependency_has_no_call (post : State) :
    ¬ Call geometry (context ∅ ∅) (before {tailFact,tailDomain}) args ⟨5⟩ ⟨6⟩ post := by
  apply surviving_ended_dependency_has_no_call
  intro h; exact (h tailFact (Or.inr (by simp [before]))).1 rfl

theorem absent_provenance_rejected :
    ¬ RequiredAtEntry (context ∅ ∅) {(before ∅) with issuedPtrs := ∅} args := by
  intro h; have issued := h.issued; simp at issued

theorem absent_backing_access_rejected :
    ¬ RequiredAtEntry (context ∅ ∅) {(before ∅) with readableRegions := ∅} args := by
  intro h; have access := h.access; simp at access

theorem nondiscardable_tail_rejected :
    ¬ RequiredAtEntry {(context ∅ ∅) with tail := {(context ∅ ∅).tail with discardable := false}}
      (before ∅) args := by
  intro h; have discard := h.discardable; simp at discard

theorem duplicate_parameter_carrier_rejected : ¬ FreshParameters (before ∅) ⟨5⟩ ⟨5⟩ :=
  fun h => h.distinct rfl

theorem nonfull_raw_fragment_rejected :
    ¬ CanDeallocate (context ∅ ∅) (finalize (eraseSlot (endRoot (transfer (before ∅) ⟨5⟩ ⟨6⟩))))
      ⟨5⟩ ⟨⟨2⟩,⟨0,0⟩⟩ := release_rejects_nonfull_or_other_region (by decide)

theorem no_second_end_or_finalize (b : F2.BindingId) :
    ¬ CanEnd (context ∅ ∅) (callPost (before ∅) ⟨5⟩ ⟨6⟩) b ∧
    ¬ CanFinalize (context ∅ ∅) (callPost (before ∅) ⟨5⟩ ⟨6⟩) b := by
  constructor <;> intro h <;> have phase := h.1 <;> simp [callPost,receiver,deallocate] at phase


end
end NewLang.Adjunct.KnownCall.Counterexample
