import NewLang.Adjunct.LiveTailProofs

namespace NewLang.Adjunct.LiveTail.Counterexample
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

private def roots : KnownCall.Context where
  head := ⟨⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨⟨1⟩,⟨0,1⟩⟩,∅,true⟩
  tail := ⟨⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨⟨2⟩,⟨0,1⟩⟩,∅,true⟩
  type := ⟨0⟩
  size := 1

private def memory : KnownCall.State where
  head := ⟨.typed,true,0⟩
  tail := ⟨.typed,true,0⟩
  carrier := fun r => match r with
    | .headAllocation => some ⟨1⟩ | .headDomain => some ⟨2⟩
    | .tailAllocation => some ⟨3⟩ | .tailDomain => some ⟨4⟩
  usedBindings := {⟨1⟩,⟨2⟩,⟨3⟩,⟨4⟩,⟨99⟩}
  externalDependencies := ∅
  blockers := ∅
  issuedPtrs := {⟨⟨1⟩,⟨1⟩⟩,⟨⟨2⟩,⟨2⟩⟩}
  readableRegions := {⟨1⟩,⟨2⟩}
  platformReady := true

private def before : State where
  world := ⟨1⟩
  roots := roots
  memory := memory
  layout := ⟨⟨3⟩,⟨3⟩⟩
  link := ⟨some (⟨1⟩,⟨⟨2⟩,⟨2⟩⟩),⟨30⟩,some ⟨7⟩,some ⟨40⟩⟩
  stage := .donor
  bundle := none
  headScope := ⟨99⟩
  scopes := {⟨99⟩}
  writableRegions := {⟨1⟩}
  ptrDependencies := ∅
  allocationDependencies := ∅
  domainDependencies := ∅
  externalDependencies := ∅
  usedFacts := {⟨1⟩,⟨2⟩,⟨30⟩,⟨40⟩,⟨90⟩}
  usedOccurrences := {⟨7⟩,⟨90⟩}

private def args : Arguments :=
  ⟨⟨1⟩,⟨⟨⟨⟨2⟩,⟨2⟩⟩,⟨⟨2⟩,⟨true,true⟩⟩⟩,⟨2⟩,⟨3⟩,⟨2⟩,⟨4⟩⟩⟩
private def headRef : HeadRef := ⟨⟨1⟩,⟨⟨1⟩,⟨1⟩⟩,⟨⟨3⟩,⟨3⟩⟩,⟨1⟩,⟨99⟩,true,true⟩
private def plan : Plan := ⟨⟨5⟩,⟨6⟩,⟨7⟩,⟨8⟩,⟨9⟩,⟨10⟩,⟨11⟩,⟨12⟩,⟨100⟩,⟨101⟩⟩
private def returned := producerPost before plan
private def afterScope := closeHeadScope returned
private def result := makeBundle before plan.returnPlacement plan.returnA plan.returnD
private def unpacked := unpack afterScope ⟨13⟩ ⟨14⟩
private def receiverArgs : Arguments := ⟨⟨1⟩,{args.tail with allocationBinding := ⟨13⟩,domainBinding := ⟨14⟩}⟩
private def finished := terminalPost unpacked ⟨15⟩ ⟨16⟩

private theorem valid : KnownCall.ContextValid geometry roots := by
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
  · decide

private theorem memoryInvariant : KnownCall.WellFormed roots memory := by
  constructor
  · intro i; cases i <;> simp [memory,KnownCall.allocationRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [memory,KnownCall.domainRole,KnownCall.State.cell]
  · intro i; cases i <;> simp [memory,KnownCall.State.cell]
  · intro i; cases i <;> simp [memory,KnownCall.State.cell]
  · intro i; cases i <;> simp [memory,KnownCall.State.cell]
  · intro i; cases i <;> rfl
  · intro r b present
    cases r <;> simp [memory] at present <;> subst b <;> simp [memory]
  · intro r q b rb qb
    cases r <;> cases q <;> simp [memory] at rb qb ⊢ <;>
      first | rfl | (subst b; contradiction)
  · constructor
    · intro i typed f dep; cases i <;> simp [roots,KnownCall.Context.root] at dep
    · simp [memory]

private theorem beforeInvariant : WellFormed before := by
  refine ⟨memoryInvariant,(by dsimp [LayoutValid,before,roots]; decide),⟨rfl,rfl⟩,by decide,by decide,by decide,?_,?_,?_,rfl,?_⟩
  · intro vf eq; simp [before] at eq; subst vf; decide
  · intro o eq; simp [before] at eq; subst o; decide
  · simp [DependenciesValid,survivingDependencies,before,memory]
  · intro b live; simp [before] at live; subst b; decide

/-- Definition alone grants no owner; this witness separately proves actual entry. -/
theorem actual_live_tail_producer_exists :
    ProducerCall geometry selectedBody before headRef args plan returned := by
  refine ⟨rfl,⟨valid,beforeInvariant,rfl,rfl,?_,?_,?_,?_,?_⟩,rfl⟩
  · constructor <;> first | rfl | (dsimp [before,memory,args,roots]; decide)
  · constructor <;> first | rfl | (dsimp [before,memory,headRef,roots]; decide)
  · constructor
    · decide
    · intro b member; dsimp [Plan.bindings,plan] at member
      simp at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · intro b member; simp [before,memory]
    · decide
    · decide
    · decide
  · simp [DetachGuard,survivingDependencies,before,memory,roots]
  · simp [ResultNonescape,ownerDependencies,before]

theorem returned_live_tail_preservation : WellFormed returned :=
  producer_preserves_wellFormed actual_live_tail_producer_exists

theorem return_has_original_live_identity_and_no_storage :
    returned.bundle = some result ∧ result.ptr = ⟨⟨2⟩,⟨2⟩⟩ ∧ result.region = ⟨2⟩ ∧
    result.domain = ⟨2⟩ ∧ result.copyable = false ∧ result.discardable = false ∧
    returned.memory.tail = before.memory.tail ∧
    KnownCall.responsibility returned.roots returned.memory .tail =
      some (.root ⟨0⟩ ⟨2⟩ ⟨⟨2⟩,⟨0,1⟩⟩) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem detach_preserves_roots_ends_only_link_occurrence :
    returned.link.payload = none ∧ returned.link.occurrence = none ∧
    returned.memory.head = before.memory.head ∧ returned.roots.tail = before.roots.tail ∧
    returned.roots.head.incarnation = before.roots.head.incarnation ∧
    returned.roots.head.extent = before.roots.head.extent ∧
    returned.roots.head.domain = before.roots.head.domain ∧
    returned.usedOccurrences = before.usedOccurrences := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem donor_formal_local_owners_not_duplicated :
    returned.memory.carrier .tailAllocation = some ⟨11⟩ ∧
    returned.memory.carrier .tailDomain = some ⟨12⟩ ∧
    ¬ DirectTailAvailable returned ⟨3⟩ ⟨4⟩ ∧
    ¬ DirectTailAvailable returned ⟨5⟩ ⟨6⟩ ∧
    ¬ DirectTailAvailable returned ⟨8⟩ ⟨9⟩ := by
  refine ⟨rfl,rfl,?_,?_,?_⟩ <;> simp [DirectTailAvailable,returned,producerPost,package]

private theorem origin : KnownReturnAfterScope afterScope := by
  refine ⟨returned,⟨geometry,selectedBody,before,headRef,args,plan,actual_live_tail_producer_exists⟩,?_,rfl⟩
  simp [ScopeExitGuard,survivingDependencies,returned,producerPost,package,detach,formalEntry,before,memory]

private theorem unpackInput : UnpackInput afterScope result ⟨13⟩ ⟨14⟩ := by
  refine ⟨origin,rfl,rfl,?_,?_⟩
  · exact Finset.notMem_erase _ _
  · constructor <;> dsimp [afterScope,closeHeadScope,returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,plan] <;> decide

theorem head_scope_ends_before_result_whole_destructure :
    WellFormed unpacked ∧ unpacked.bundle = none ∧
    DirectTailAvailable unpacked ⟨13⟩ ⟨14⟩ ∧ unpacked.headScope ∉ unpacked.scopes :=
  ⟨whole_destructure_preserves_wellFormed unpackInput,rfl,
    (whole_destructure_consumes_package unpackInput).2.2.1,Finset.notMem_erase _ _⟩

theorem returned_packet_cannot_be_unpacked_twice (b : Bundle) (a d : F2.BindingId) :
    ¬ UnpackInput unpacked b a d := whole_destructure_cannot_repeat unpackInput b a d

theorem independently_applicable_subsequent_receiver : TerminalCall geometry unpacked receiverArgs ⟨15⟩ ⟨16⟩ := by
  refine ⟨whole_destructure_preserves_wellFormed unpackInput,rfl,Finset.notMem_erase _ _,rfl,?_,?_⟩
  · refine ⟨(by change KnownCall.ContextValid geometry returned.roots; exact producer_preserves_context actual_live_tail_producer_exists),
      (whole_destructure_preserves_wellFormed unpackInput).memory,?_,?_,?_,rfl⟩
    · constructor <;> first | rfl | (dsimp [unpacked,unpack,afterScope,closeHeadScope,returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,plan,receiverArgs,args,roots]; decide)
    · constructor <;> dsimp [unpacked,unpack,afterScope,closeHeadScope,returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,plan] <;> decide
    · simp [KnownCall.SurvivorGuard,unpacked,unpack,afterScope,closeHeadScope,returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,roots]
  · simp [TerminalGuard,unpacked,unpack,afterScope,closeHeadScope,returned,producerPost,package,detach,formalEntry,before]

theorem terminal_ends_original_tail_once_and_keeps_head_live :
    WellFormed finished ∧ finished.memory.tail.phase = .released ∧
    finished.memory.tail.releases = 1 ∧ finished.memory.head.phase = .typed ∧
    finished.memory.carrier .headAllocation = some ⟨1⟩ ∧
    finished.memory.carrier .headDomain = some ⟨2⟩ :=
  ⟨subsequent_terminal_preserves_wellFormed independently_applicable_subsequent_receiver,
    rfl,rfl,rfl,rfl,rfl⟩

theorem terminal_cannot_resurrect_or_double_free :
    ¬ KnownCall.CurrentLocator finished.roots finished.memory ⟨⟨2⟩,⟨2⟩⟩ ∧
    ∀ a raw, ¬ KnownCall.CanDeallocate finished.roots finished.memory a raw :=
  subsequent_terminal_no_resurrection_or_double_release independently_applicable_subsequent_receiver

/-- Same static parameter types, different original identities. -/
theorem wrong_domain_rejected :
    ¬ ActualCallApplicable geometry before headRef {args with tail := {args.tail with domain := ⟨1⟩}} plan :=
  wrong_domain_rejects_call (by decide)

theorem wrong_region_rejected :
    ¬ ActualCallApplicable geometry before headRef {args with tail := {args.tail with allocationRegion := ⟨1⟩}} plan :=
  wrong_region_rejects_call (by decide)

theorem head_ptr_is_not_tail_owner :
    ¬ ActualCallApplicable geometry before headRef
      {args with tail := {args.tail with ptr := {args.tail.ptr with token := ⟨⟨1⟩,⟨1⟩⟩}}} plan := by
  intro h; have eq := h.tail.ptrRoot; cases eq

theorem stale_tail_incarnation_rejected :
    ¬ ActualCallApplicable geometry before headRef
      {args with tail := {args.tail with ptr := {args.tail.ptr with token := ⟨⟨2⟩,⟨9⟩⟩}}} plan := by
  intro h; have eq := h.tail.ptrRoot; cases eq

theorem none_head_link_rejected :
    ¬ ActualCallApplicable geometry {before with link := {before.link with payload := none}} headRef args plan :=
  wrong_current_link_rejects_call (by decide)

theorem other_some_head_link_rejected :
    ¬ ActualCallApplicable geometry
      {before with link := {before.link with payload := some (⟨1⟩,⟨⟨1⟩,⟨1⟩⟩)}} headRef args plan :=
  wrong_current_link_rejects_call (by decide)

theorem foreign_world_numeric_identity_rejected :
    ¬ ActualCallApplicable geometry before headRef {args with world := ⟨2⟩} plan ∧
    ¬ ActualCallApplicable geometry
      {before with link := {before.link with payload := some (⟨2⟩,args.tail.ptr.token)}} headRef args plan :=
  ⟨wrong_world_rejects_call (by decide),wrong_current_link_rejects_call (by decide)⟩

theorem foreign_head_ref_rejected :
    ¬ ActualCallApplicable geometry before {headRef with world := ⟨2⟩} args plan := by
  intro h; have eq := h.head.world; cases eq

theorem wrong_fixed_field_rejected :
    ¬ ActualCallApplicable geometry before {headRef with field := ⟨⟨4⟩,⟨4⟩⟩} args plan := by
  intro h; have eq := h.head.field; cases eq

theorem readonly_head_ref_rejected :
    ¬ ActualCallApplicable geometry before {headRef with write := false} args plan :=
  readonly_head_ref_rejects_call rfl

theorem expired_scope_rejected :
    ¬ ActualCallApplicable geometry {before with scopes := ∅} headRef args plan :=
  expired_head_scope_rejects_call (Finset.notMem_empty _)

theorem missing_head_write_access_rejected :
    ¬ ActualCallApplicable geometry {before with writableRegions := ∅} headRef args plan := by
  intro h; exact Finset.notMem_empty _ h.head.writeAccess

theorem copied_ptr_cannot_mint_missing_owners :
    ¬ ActualCallApplicable geometry
      {before with memory := {memory with carrier := fun r =>
        if r = .tailAllocation ∨ r = .tailDomain then none else memory.carrier r}} headRef args plan := by
  intro h; have owner := h.tail.allocation; simp at owner

theorem unavailable_domain_owner_rejected :
    ¬ ActualCallApplicable geometry
      {before with memory := {memory with carrier := fun r =>
        if r = .tailDomain then none else memory.carrier r}} headRef args plan := by
  intro h; have owner := h.tail.domain; simp at owner

theorem head_scoped_dependency_cannot_escape_in_owner :
    ¬ ActualCallApplicable geometry
      {before with allocationDependencies := {.scope ⟨99⟩}} headRef args plan :=
  escaping_owner_dependency_rejects_call (scope := ⟨99⟩) (by decide)
    (by simp [ownerDependencies,before])

private theorem externalInvariant (dep : Dependency) (live : DependencyLive before dep) :
    WellFormed {before with externalDependencies := {dep}} := by
  refine ⟨beforeInvariant.memory,beforeInvariant.layout,beforeInvariant.shape,
    beforeInvariant.parentRecorded,beforeInvariant.tailRecorded,beforeInvariant.linkRecorded,
    beforeInvariant.payloadRecorded,beforeInvariant.occurrenceRecorded,?_,rfl,beforeInvariant.scopeRecorded⟩
  intro d member
  have same : d = dep := by simpa [survivingDependencies,before,memory] using member
  subst d; exact live

/-- Valid pre-state; only the proposed head Change/Reset ends this dependency. -/
theorem old_occurrence_survivor_is_live_but_rejects_return :
    WellFormed {before with externalDependencies := {.memory (.occurrence ⟨7⟩)}} ∧
    ¬ ActualCallApplicable geometry
      {before with externalDependencies := {.memory (.occurrence ⟨7⟩)}} headRef args plan := by
  refine ⟨externalInvariant _ ⟨rfl,rfl⟩,?_⟩
  exact ended_link_dependency_rejects_call (f := .occurrence ⟨7⟩)
    (by simp [survivingDependencies,before,memory]) rfl

theorem old_field_current_dependency_rejected :
    ¬ ActualCallApplicable geometry
      {before with externalDependencies := {.memory (.fixed (.valueFact ⟨3⟩ ⟨30⟩))}} headRef args plan :=
  ended_link_dependency_rejects_call (f := .fixed (.valueFact ⟨3⟩ ⟨30⟩)) (by simp [survivingDependencies,before,memory]) (Or.inr ⟨rfl,rfl⟩)

theorem old_parent_current_dependency_rejected :
    ¬ ActualCallApplicable geometry
      {before with externalDependencies := {.memory (.fixed (.valueFact ⟨1⟩ ⟨1⟩))}} headRef args plan :=
  ended_link_dependency_rejects_call (f := .fixed (.valueFact ⟨1⟩ ⟨1⟩)) (by simp [survivingDependencies,before,memory]) (Or.inl ⟨rfl,rfl⟩)

theorem historical_fact_reuse_rejected :
    ¬ ActualCallApplicable geometry before headRef args {plan with parentFact := ⟨90⟩} := by
  intro h; exact h.fresh.parentFresh (by decide)

theorem duplicate_result_field_carrier_rejected :
    ¬ ActualCallApplicable geometry before headRef args {plan with returnD := plan.returnA} := by
  intro h; have distinct := h.fresh.distinct
  have impossible : ¬ ({plan with returnD := plan.returnA}).bindings.Nodup := by decide
  exact impossible distinct

theorem missing_constructor_field_rejected :
    ¬ DefinitionChecked [.detach,.construct [.ptr,.allocation],.returnValue] := by dsimp [DefinitionChecked,selectedBody]; decide

theorem duplicate_constructor_field_rejected :
    ¬ DefinitionChecked [.detach,.construct [.ptr,.allocation,.allocation],.returnValue] := by dsimp [DefinitionChecked,selectedBody]; decide

theorem finishing_tail_is_not_live_return_definition :
    ¬ DefinitionChecked [.detach,.finishTail,.construct [.ptr,.allocation,.domain],.returnValue] := by dsimp [DefinitionChecked,selectedBody]; decide

theorem rejected_actual_entry_does_not_publish_or_consume :
    checkedProducer geometry selectedBody before headRef
      {args with tail := {args.tail with domain := ⟨1⟩}} plan = (before,none) :=
  rejected_call_preserves_public_state (fun h => wrong_domain_rejected h.2)

theorem bad_constructor_does_not_publish_or_consume :
    checkedProducer geometry [.detach,.construct [.ptr,.allocation],.returnValue]
      before headRef args plan = (before,none) :=
  rejected_call_preserves_public_state (fun h => missing_constructor_field_rejected h.1)

theorem nominal_bundle_cannot_certify_wrong_original_region :
    ¬ CarriesLiveH returned {result with region := ⟨1⟩} :=
  mismatched_bundle_region_has_no_certificate (by decide)

theorem nominal_bundle_cannot_supply_missing_domain_carrier :
    ¬ CarriesLiveH {returned with memory := {(returned.memory) with carrier := (fun r =>
      if r = .tailDomain then none else returned.memory.carrier r)}} result :=
  missing_bundle_domain_carrier_has_no_certificate (by simp)

theorem earlier_terminal_post_is_not_still_live_return :
    ¬ CarriesLiveH {before with memory := KnownCall.callPost memory ⟨5⟩ ⟨6⟩} result :=
  ended_root_has_no_live_return_certificate rfl

/-- A terminal receiver needs its own guard; producer legality does not grant it. -/
theorem still_live_tail_dependency_is_not_terminal_permission :
    DependencyLive before (.memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩))) ∧
    ¬ TerminalGuard {before with externalDependencies := {.memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩))}} := by
  refine ⟨Or.inl ⟨.tail,rfl,rfl,rfl⟩,?_⟩
  intro guard
  exact (guard _ (by simp [before,roots]) _ rfl).1 rfl

/-- If the detach guard is deleted, the raw candidate retains a dead dependency. -/
theorem unchecked_detach_breaks_occurrence_dependency :
    ¬ DependenciesValid (producerPost
      {before with externalDependencies := {.memory (.occurrence ⟨7⟩)}} plan) := by
  intro deps
  have live := deps (.memory (.occurrence ⟨7⟩)) (by
    simp [survivingDependencies,producerPost,package,detach,formalEntry,before,memory])
  have present := live.2
  change none = some _ at present
  cases present

theorem clearing_some_without_ending_occurrence_breaks_shape :
    ¬ WellFormed {before with link := {before.link with payload := none}} := by
  intro wf; have shape := wf.shape.1; change false = true at shape; cases shape

/-- A role-view permutation for a concrete caller cleanup, not relocation and
not a second direct Call (whose earlier bounded entry requires both roots live). -/
private def swapContext (c : KnownCall.Context) : KnownCall.Context :=
  {c with head := c.tail,tail := c.head}
private def swapMemory (s : KnownCall.State) : KnownCall.State :=
  {s with head := s.tail,tail := s.head,carrier := fun r => match r with
    | .headAllocation => s.carrier .tailAllocation
    | .headDomain => s.carrier .tailDomain
    | .tailAllocation => s.carrier .headAllocation
    | .tailDomain => s.carrier .headDomain}
private def headView := swapMemory finished.memory
private def cleaned := swapMemory (KnownCall.receiver headView)

/-- Every primitive applicability condition is proved before separately freeing
head: the original head A/D and full extent, no surviving governed root. -/
theorem caller_can_separately_end_and_release_head :
    finished.headScope ∉ finished.scopes ∧
    KnownCall.CanEnd (swapContext finished.roots) headView ⟨2⟩ ∧
    KnownCall.CanEraseSlot (KnownCall.endRoot headView) ∧
    KnownCall.CanFinalize (swapContext finished.roots)
      (KnownCall.eraseSlot (KnownCall.endRoot headView)) ⟨2⟩ ∧
    KnownCall.CanDeallocate (swapContext finished.roots)
      (KnownCall.finalize (KnownCall.eraseSlot (KnownCall.endRoot headView)))
      ⟨1⟩ before.roots.head.extent := by
  refine ⟨Finset.notMem_erase _ _,?_,rfl,?_,?_⟩
  · dsimp [KnownCall.CanEnd,swapContext,headView,swapMemory,finished,terminalPost,
      KnownCall.callPost,KnownCall.receiver,KnownCall.deallocate,KnownCall.finalize,
      KnownCall.eraseSlot,KnownCall.endRoot,unpacked,unpack,afterScope,closeHeadScope,
      returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,roots]
    decide
  · refine ⟨rfl,rfl,rfl,Finset.notMem_empty _,?_,?_⟩
    · intro o governing
      rcases governing with ⟨i,typed,_,_⟩
      cases i <;> cases typed
    · intro f member
      have empty : finished.roots.tail.dependencies = ∅ ∧ headView.externalDependencies = ∅ := ⟨rfl,rfl⟩
      simp [swapContext,KnownCall.eraseSlot,KnownCall.endRoot,empty.1,empty.2] at member
  · dsimp [KnownCall.CanDeallocate,swapContext,headView,swapMemory,finished,terminalPost,
      KnownCall.callPost,KnownCall.receiver,KnownCall.deallocate,KnownCall.finalize,
      KnownCall.eraseSlot,KnownCall.endRoot,unpacked,unpack,afterScope,closeHeadScope,
      returned,producerPost,package,detach,formalEntry,KnownCall.transfer,before,memory,roots]
    decide

theorem separate_cleanup_releases_each_original_root_once :
    cleaned.head.phase = .released ∧ cleaned.tail.phase = .released ∧
    cleaned.head.releases = 1 ∧ cleaned.tail.releases = 1 ∧
    (∀ r, cleaned.carrier r = none) ∧
    KnownCall.responsibility finished.roots cleaned .head = none ∧
    KnownCall.responsibility finished.roots cleaned .tail = none := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl⟩
  intro r; cases r <;> rfl

theorem separate_cleanup_preserves_accounting : KnownCall.WellFormed finished.roots cleaned := by
  constructor
  · intro i; cases i <;> simp [KnownCall.allocationRole,KnownCall.State.cell,separate_cleanup_releases_each_original_root_once.2.2.2.2.1]
    <;> rfl
  · intro i; cases i <;> simp [KnownCall.domainRole,KnownCall.State.cell,separate_cleanup_releases_each_original_root_once.2.2.2.2.1]
    <;> rfl
  · intro i; cases i <;> change (KnownCall.Phase.released = .typed → false = true) <;> simp
  · intro i; cases i <;> change (KnownCall.Phase.released = .emptySlot → false = true) <;> simp
  · intro i; cases i <;> intro h <;> rfl
  · intro i; cases i <;> rfl
  · intro r b present
    rw [separate_cleanup_releases_each_original_root_once.2.2.2.2.1] at present
    cases present
  · intro r q b present other
    rw [separate_cleanup_releases_each_original_root_once.2.2.2.2.1] at present
    cases present
  · constructor
    · intro i typed; cases i <;> cases typed
    · change ∀ f ∈ (∅ : Finset F0.Fact), _; simp

private def tailObserver : State :=
  {before with externalDependencies := {.memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩))}}

/-- Producer is legal with a live tail-current observer, but that same survivor
requires a separate rejection at the terminal receiver boundary. -/
theorem live_return_is_not_an_automatic_terminal_grant :
    ProducerCall geometry selectedBody tailObserver headRef args plan (producerPost tailObserver plan) ∧
    ¬ TerminalGuard (unpack (closeHeadScope (producerPost tailObserver plan)) ⟨13⟩ ⟨14⟩) := by
  have entry := actual_live_tail_producer_exists.2.1
  refine ⟨⟨rfl,⟨entry.context,externalInvariant _ (Or.inl ⟨.tail,rfl,rfl,rfl⟩),
    entry.donor,entry.world,entry.tail,⟨entry.head.world,entry.head.root,entry.head.field,entry.head.governing,entry.head.scopeIdentity,entry.head.liveScope,entry.head.read,entry.head.write,entry.head.readAccess,entry.head.writeAccess,entry.head.someExactTail⟩,
    ⟨entry.fresh.distinct,entry.fresh.unused,entry.fresh.valueScopes,entry.fresh.parentFresh,entry.fresh.linkFresh,entry.fresh.differentFacts⟩,?_,entry.nonescape⟩,rfl⟩,?_⟩
  · constructor
    · simp [tailObserver,roots,memory,before]
    · intro dep member f eq
      have same : dep = .memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩)) := by
        simpa [survivingDependencies,tailObserver,before,memory] using member
      rw [same] at eq
      have fact := (Dependency.memory.inj eq).symm
      subst f
      dsimp [EndsAtDetach,tailObserver,before,roots]
      decide
  · intro guard
    exact (guard _ (by
      simp [unpack,closeHeadScope,producerPost,package,detach,formalEntry,tailObserver,before,roots]) _ rfl).1 rfl

/-- Dependencies are carried unchanged; a still-live tail-domain dependency is
allowed in the returned owner, rather than erased at the return boundary. -/
theorem returned_owner_keeps_a_nonempty_live_dependency :
    let s : State := {before with allocationDependencies := {Dependency.memory (.fixed (.domainLive ⟨2⟩))}}
    ProducerCall geometry selectedBody s headRef args plan (producerPost s plan) ∧
    (makeBundle s plan.returnPlacement plan.returnA plan.returnD).dependencies =
      {.memory (.fixed (.domainLive ⟨2⟩))} := by
  dsimp only
  let s : State := {before with allocationDependencies := {Dependency.memory (.fixed (.domainLive ⟨2⟩))}}
  have wf : WellFormed s := by
    refine ⟨beforeInvariant.memory,beforeInvariant.layout,beforeInvariant.shape,
      beforeInvariant.parentRecorded,beforeInvariant.tailRecorded,beforeInvariant.linkRecorded,
      beforeInvariant.payloadRecorded,beforeInvariant.occurrenceRecorded,?_,rfl,beforeInvariant.scopeRecorded⟩
    intro dep member
    have same : dep = .memory (.fixed (.domainLive ⟨2⟩)) := by
      simpa [survivingDependencies,s,before,memory] using member
    subst dep
    exact ⟨.tail,rfl,rfl⟩
  have entry := actual_live_tail_producer_exists.2.1
  refine ⟨⟨rfl,⟨entry.context,wf,entry.donor,entry.world,entry.tail,⟨entry.head.world,entry.head.root,entry.head.field,entry.head.governing,entry.head.scopeIdentity,entry.head.liveScope,entry.head.read,entry.head.write,entry.head.readAccess,entry.head.writeAccess,entry.head.someExactTail⟩,
    ⟨entry.fresh.distinct,entry.fresh.unused,entry.fresh.valueScopes,entry.fresh.parentFresh,entry.fresh.linkFresh,entry.fresh.differentFacts⟩,?_,?_⟩,rfl⟩,?_⟩
  · constructor
    · simp [roots,memory,before]
    · intro dep member f eq
      have same : dep = .memory (.fixed (.domainLive ⟨2⟩)) := by
        simpa [survivingDependencies,s,before,memory] using member
      rw [same] at eq
      have fact := (Dependency.memory.inj eq).symm
      subst f
      exact id
  · intro b live; simp [ownerDependencies,before]
  · simp [makeBundle,ownerDependencies,before]

theorem live_head_binding_cannot_be_reused_for_return :
    ¬ ActualCallApplicable geometry before headRef args {plan with returnPlacement := ⟨99⟩} := by
  intro h
  exact h.fresh.unused ⟨99⟩ (by simp [Plan.bindings]) (h.pre.scopeRecorded ⟨99⟩ (by decide))

/-- The three affine carrier boundaries do not end or replace the heap root. -/
theorem each_producer_boundary_retains_original_tail :
    (formalEntry before plan).memory.carrier .tailAllocation = some ⟨5⟩ ∧
    (formalEntry before plan).memory.carrier .tailDomain = some ⟨6⟩ ∧
    (package (detach (formalEntry before plan) plan) ⟨7⟩ ⟨8⟩ ⟨9⟩ .localBundle).memory.carrier .tailAllocation = some ⟨8⟩ ∧
    (package (detach (formalEntry before plan) plan) ⟨7⟩ ⟨8⟩ ⟨9⟩ .localBundle).memory.carrier .tailDomain = some ⟨9⟩ ∧
    (formalEntry before plan).memory.tail = before.memory.tail ∧
    (package (detach (formalEntry before plan) plan) ⟨7⟩ ⟨8⟩ ⟨9⟩ .localBundle).memory.tail = before.memory.tail ∧
    returned.memory.tail = before.memory.tail := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Removing only the survivor check leaves owner accounting intact, isolating
why occurrence validation is necessary rather than an arbitrary new prohibition. -/
theorem unchecked_detach_keeps_owners_but_breaks_dependencies :
    let post := producerPost {before with externalDependencies := {.memory (.occurrence ⟨7⟩)}} plan
    KnownCall.WellFormed post.roots post.memory ∧ ¬ DependenciesValid post :=
  ⟨returned_live_tail_preservation.memory,unchecked_detach_breaks_occurrence_dependency⟩

theorem definition_certificate_does_not_grant_mismatched_entry :
    ConditionalDefinition geometry selectedBody ∧
    ¬ ActualCallApplicable geometry before headRef {args with tail := {args.tail with domain := ⟨1⟩}} plan :=
  ⟨selected_producer_definition_is_conditional geometry,wrong_domain_rejected⟩

theorem caller_final_snapshot_wellFormed : WellFormed {finished with memory := cleaned} := by
  have wf := terminal_ends_original_tail_once_and_keeps_head_live.1
  refine ⟨separate_cleanup_preserves_accounting,wf.layout,wf.shape,wf.parentRecorded,wf.tailRecorded,
    wf.linkRecorded,wf.payloadRecorded,wf.occurrenceRecorded,?_,rfl,wf.scopeRecorded⟩
  simp [DependenciesValid,survivingDependencies,finished,terminalPost,unpacked,unpack,afterScope,
    closeHeadScope,returned,producerPost,package,detach,formalEntry,before]

theorem receiver_cannot_bypass_whole_destructure (g : Geometry) (a : Arguments) (x y : F2.BindingId) :
    ¬ TerminalCall g returned a x y := by
  intro call; have stage := call.2.1; cases stage

theorem receiver_cannot_run_again (a : Arguments) (x y : F2.BindingId) :
    ¬ TerminalCall geometry {finished with stage := .unpacked} a x y := by
  intro call; have live := call.2.2.2.2.1.2.2.1.live; cases live

end
end NewLang.Adjunct.LiveTail.Counterexample
