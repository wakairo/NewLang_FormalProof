import NewLang.Adjunct.CustodyProofs

namespace NewLang.Adjunct.Custody.Counterexample
open F0 F1.Backing F1.Occupancy
noncomputable section
namespace Source
open LiveTail
def geometry : Geometry where
  capacity := fun _ => 1
  byteAt := fun r n => ⟨r.index * 10 + n⟩
  injective := by
    intro r a b eq
    have same := congrArg AbstractByteId.index eq
    dsimp at same
    omega

def roots : KnownCall.Context where
  head := ⟨⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨1⟩,⟨⟨1⟩,⟨0,1⟩⟩,∅,true⟩
  tail := ⟨⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨2⟩,⟨⟨2⟩,⟨0,1⟩⟩,∅,true⟩
  type := ⟨0⟩
  size := 1

def memory : KnownCall.State where
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

def before : LiveTail.State where
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

def args : Arguments :=
  ⟨⟨1⟩,⟨⟨⟨⟨2⟩,⟨2⟩⟩,⟨⟨2⟩,⟨true,true⟩⟩⟩,⟨2⟩,⟨3⟩,⟨2⟩,⟨4⟩⟩⟩
def headRef : HeadRef := ⟨⟨1⟩,⟨⟨1⟩,⟨1⟩⟩,⟨⟨3⟩,⟨3⟩⟩,⟨1⟩,⟨99⟩,true,true⟩
def plan : Plan := ⟨⟨5⟩,⟨6⟩,⟨7⟩,⟨8⟩,⟨9⟩,⟨10⟩,⟨11⟩,⟨12⟩,⟨100⟩,⟨101⟩⟩
def returned := producerPost before plan
def afterScope := closeHeadScope returned
def result := makeBundle before plan.returnPlacement plan.returnA plan.returnD

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

private theorem beforeInvariant : LiveTail.WellFormed before := by
  refine ⟨memoryInvariant,(by dsimp [LayoutValid,before,roots]; decide),⟨rfl,rfl⟩,by decide,by decide,by decide,?_,?_,?_,rfl,?_⟩
  · intro vf eq; simp [before] at eq; subst vf; decide
  · intro o eq; simp [before] at eq; subst o; decide
  · simp [LiveTail.DependenciesValid,survivingDependencies,before,memory]
  · intro b live; simp [before] at live; subst b; decide

/-- Definition alone grants no owner; this witness separately proves actual entry. -/
theorem producer_exists :
    ProducerCall geometry LiveTail.selectedBody before headRef args plan returned := by
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


private theorem returnedInvariant : LiveTail.WellFormed returned :=
  LiveTail.producer_preserves_wellFormed producer_exists

theorem origin : LiveTail.KnownReturnAfterScope afterScope := by
  refine ⟨returned,⟨geometry,LiveTail.selectedBody,before,headRef,args,plan,producer_exists⟩,?_,rfl⟩
  simp [LiveTail.ScopeExitGuard,LiveTail.survivingDependencies,returned,LiveTail.producerPost,
    LiveTail.package,LiveTail.detach,LiveTail.formalEntry,before,memory]
end Source

private def container : LocalRoot := ⟨⟨50⟩,⟨50⟩,⟨50⟩,⟨50⟩,⟨30⟩,true,true⟩
private def initial : State where
  heap := {Source.afterScope with
    stage := .consumed,bundle := none,
    memory := {(Source.afterScope.memory) with usedBindings := insert ⟨30⟩ Source.afterScope.memory.usedBindings}}
  approved := Source.afterScope
  container := container
  available := true
  tag := .none
  currentFact := ⟨200⟩
  occurrence := none
  payloadFact := none
  packet := Source.result
  holders := {.packet}
  oldSum := none
  knowledge := .initializedNone ⟨200⟩
  choice := .pending
  route := .beforeAdopt
  loans := ∅
  aliases := []
  extraDependencies := ∅
  usedFacts := insert ⟨200⟩ Source.afterScope.usedFacts
  usedOccurrences := Source.afterScope.usedOccurrences

private def beforeAdopt := openLoan initial ⟨31⟩
private def sink : Sink := ⟨⟨1⟩,container,⟨31⟩,true,true⟩
private def adoptPlan : AdoptPlan := ⟨⟨⟨33⟩,⟨34⟩,⟨35⟩⟩,⟨⟨36⟩,⟨37⟩,⟨38⟩⟩,⟨32⟩,⟨201⟩,⟨202⟩,⟨50⟩⟩
private def adopted := recipientPost beforeAdopt adoptPlan
private def afterRecipient := closeLoan adopted ⟨31⟩
private def beforeExtract := openLoan afterRecipient ⟨39⟩
private def extractionSink : Sink := {sink with scope := ⟨39⟩}
private def extractPlan : ExtractPlan := ⟨⟨⟨40⟩,⟨41⟩,⟨42⟩⟩,⟨203⟩⟩
private def extracted := extractPost beforeExtract extractPlan
private def afterExtract := closeLoan extracted ⟨39⟩
private def savedSupply : Supply := ⟨⟨43⟩,⟨44⟩,⟨45⟩⟩
private def recovered := recoverPost afterExtract savedSupply
private def unpackSupply : Supply := ⟨⟨46⟩,⟨47⟩,⟨48⟩⟩
private def unpacked := unpackPost recovered unpackSupply
private def finished := terminalPost unpacked ⟨52⟩ ⟨53⟩
private def completed := consumeFinalNone finished

-- Only finite computations, no executable source checker or native allocator claim.
private theorem initialInvariant : WellFormed Source.geometry initial := by
  have old := LiveTail.known_return_after_scope_is_wellFormed Source.origin
  have producer := Source.producer_exists
  have heap : LiveTail.WellFormed initial.heap := by
    have k := old.memory
    refine ⟨⟨k.allocation,k.domain,k.typedDomain,k.slotDomain,k.releasedDomain,k.releaseCount,
      (fun r b h => Finset.mem_insert_of_mem (k.recorded r b h)),k.unique,k.dependencies⟩,
      old.layout,old.shape,old.parentRecorded,old.tailRecorded,old.linkRecorded,old.payloadRecorded,
      old.occurrenceRecorded,old.dependencies,rfl,?_⟩
    intro b live; exact Finset.mem_insert_of_mem (old.scopeRecorded b live)
  refine ⟨⟨heap,⟨rfl,rfl⟩,?_,Source.origin,rfl,rfl,?_,?_,by decide,
    (fun _ => ⟨.packet,rfl⟩),?_,?_,(fun _ => by decide),?_⟩,
    by decide,?_,?_,⟨rfl,rfl,rfl⟩,⟨by simp [initial],by simp [initial]⟩,?_,?_,?_,?_⟩
  · change KnownCall.ContextValid Source.geometry Source.returned.roots
    exact LiveTail.producer_preserves_context producer
  · exact ⟨Source.result,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · dsimp [LocalDistinct,initial,container,Source.afterScope,LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,LiveTail.formalEntry,rehome,Source.before,Source.roots]; decide
  · intro bad; change KnownCall.Phase.typed = .released at bad; cases bad
  · intro _; constructor <;> first | rfl | decide
  · intro _ r; cases r <;> decide
  · intro o bad; cases bad
  · intro vf bad; cases bad
  · simp [initial]
  · simp [initial]
  · simp [DependenciesValid,initial]
  · intro bad; cases bad

private theorem beforeInvariant : WellFormed Source.geometry beforeAdopt :=
  opening_local_loan_preserves_wellFormed initialInvariant _

private theorem readyBefore : ReadyPacket beforeAdopt := by
  constructor <;> first | rfl | decide

/-- The definition certificate does not assert an actual arbitrary call is valid. -/
theorem independent_recipient_definition_checked : ConditionalDefinition Source.geometry selectedBody :=
  recipient_definition_is_conditional _

theorem actual_recipient_call : RecipientCall Source.geometry selectedBody beforeAdopt sink adoptPlan adopted := by
  refine ⟨rfl,⟨beforeInvariant,by decide,rfl,rfl,rfl,Or.inl rfl,?_,readyBefore,?_,?_,?_,?_,?_,?_,?_⟩,rfl⟩
  · constructor <;> first | rfl | decide
  · refine ⟨by decide,?_,?_,by decide,by decide,by decide,by decide⟩
    · intro b mem
      simp [AdoptPlan.bindings,adoptPlan] at mem
      rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    · intro b mem; simp [beforeAdopt,openLoan,initial,Source.afterScope,LiveTail.closeHeadScope,
        Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,LiveTail.formalEntry,
        Source.before,Source.memory,KnownCall.transfer]
  · exact ⟨by decide,by decide,by decide⟩
  · simp [ChangeGuard,beforeAdopt,openLoan,initial]
  · simp [ScopeGuard,beforeAdopt,openLoan,initial,LiveTail.ownerDependencies,Source.afterScope,
      LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,
      LiveTail.formalEntry,Source.before]
  · simp [ScopeGuard,beforeAdopt,openLoan,initial,LiveTail.ownerDependencies,Source.afterScope,
      LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,
      LiveTail.formalEntry,Source.before]
  · decide
  · simp [ScopeGuard,beforeAdopt,openLoan,initial,LiveTail.ownerDependencies,Source.afterScope,
      LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,
      LiveTail.formalEntry,Source.before]

private theorem adoptedInvariant : WellFormed Source.geometry adopted :=
  recipient_preserves_wellFormed actual_recipient_call
private theorem adoptedScopeGuard : ScopeGuard adopted ⟨31⟩ := by
  simp [ScopeGuard,adopted,recipientPost,consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,
    openLoan,initial,LiveTail.ownerDependencies,Source.afterScope,LiveTail.closeHeadScope,
    Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,LiveTail.formalEntry,Source.before]
private theorem afterRecipientInvariant : WellFormed Source.geometry afterRecipient :=
  closing_local_loan_preserves_wellFormed adoptedInvariant adoptedScopeGuard
private theorem beforeExtractInvariant : WellFormed Source.geometry beforeExtract :=
  opening_local_loan_preserves_wellFormed afterRecipientInvariant _

/-- Recipient frame has returned and its loan is gone; both original roots live. -/
theorem recipient_returns_unit_with_live_tail_in_caller_custody :
    WellFormed Source.geometry afterRecipient ∧ afterRecipient.holders = {.custody} ∧
    afterRecipient.tag = .some ∧ afterRecipient.heap.memory.tail.phase = .typed ∧
    afterRecipient.heap.memory.tail.releases = 0 ∧ afterRecipient.heap.memory.head.releases = 0 ∧
    afterRecipient.loans = ∅ ∧ afterRecipient.container = initial.container ∧
    afterRecipient.packet.ptr = initial.packet.ptr ∧ afterRecipient.packet.region = initial.packet.region ∧
    afterRecipient.packet.domain = initial.packet.domain :=
  ⟨afterRecipientInvariant,rfl,rfl,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl⟩

theorem actual_delayed_extract : ExtractApplicable Source.geometry beforeExtract extractionSink extractPlan := by
  refine ⟨beforeExtractInvariant,?_,rfl,Or.inl rfl,Or.inl rfl,?_,?_,by decide,by decide,?_,?_,?_⟩
  · constructor <;> first | rfl | decide
  · intro bad; cases bad
  · refine ⟨by decide,?_,by decide,by decide⟩
    constructor <;> decide
  · intro _; constructor <;> first | rfl | decide
  · simp [ChangeGuard,beforeExtract,openLoan,afterRecipient,closeLoan,adopted,recipientPost,
      consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,initial]
  · simp [ScopeGuard,beforeExtract,openLoan,afterRecipient,closeLoan,adopted,recipientPost,
      consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,initial,LiveTail.ownerDependencies,
      Source.afterScope,LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,
      LiveTail.package,LiveTail.detach,LiveTail.formalEntry,Source.before]
private theorem extractedInvariant : WellFormed Source.geometry extracted :=
  extraction_preserves_wellFormed actual_delayed_extract
private theorem extractedScopeGuard : ScopeGuard extracted ⟨39⟩ := by
  simp [ScopeGuard,extracted,extractPost,beforeExtract,openLoan,afterRecipient,closeLoan,adopted,
    recipientPost,consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,initial,
    LiveTail.ownerDependencies,Source.afterScope,LiveTail.closeHeadScope,Source.returned,
    LiveTail.producerPost,LiveTail.package,LiveTail.detach,LiveTail.formalEntry,Source.before]
private theorem afterExtractInvariant : WellFormed Source.geometry afterExtract :=
  closing_local_loan_preserves_wellFormed extractedInvariant extractedScopeGuard

theorem actual_exhaustive_saved_match : RecoverApplicable Source.geometry afterExtract savedSupply := by
  refine ⟨afterExtractInvariant,⟨⟨.some,.extraction,.unknown,⟨201⟩⟩,rfl,rfl⟩,
    by decide,rfl,rfl,?_,?_⟩
  · refine ⟨by decide,?_,by decide,by decide⟩
    constructor <;> decide
  · intro _; constructor <;> first | rfl | decide
private theorem recoveredInvariant : WellFormed Source.geometry recovered :=
  recovery_preserves_wellFormed actual_exhaustive_saved_match

theorem original_packet_extracted_without_occurrence_transfer :
    WellFormed Source.geometry recovered ∧ recovered.holders = {.saved} ∧
    recovered.occurrence = none ∧ recovered.payloadFact = none ∧
    recovered.packet.ptr = initial.packet.ptr ∧ recovered.packet.region = initial.packet.region ∧
    recovered.packet.domain = initial.packet.domain ∧ recovered.packet.dependencies = initial.packet.dependencies ∧
    recovered.heap.roots = initial.heap.roots ∧ recovered.heap.memory.tail.phase = .typed ∧
    recovered.heap.memory.tail.releases = 0 ∧ recovered.tag = .none :=
  ⟨recoveredInvariant,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_whole_packet_unpack : UnpackApplicable Source.geometry recovered unpackSupply := by
  refine ⟨recoveredInvariant,Or.inl (by decide),Or.inl ⟨rfl,by decide⟩,by decide,rfl,rfl,?_,?_⟩
  · refine ⟨by decide,?_,by decide,by decide⟩
    constructor <;> decide
  · constructor <;> first | rfl | decide
private theorem unpackedInvariant : WellFormed Source.geometry unpacked :=
  unpacking_preserves_wellFormed actual_whole_packet_unpack

/-- This terminal receiver separately proves RequiredAtEntry on the current
whole-unpacked original fields; static LiveTail types alone do not supply it. -/
theorem actual_independent_terminal_receiver : TerminalApplicable Source.geometry unpacked ⟨52⟩ ⟨53⟩ := by
  refine ⟨unpackedInvariant,by decide,Or.inl rfl,by decide,rfl,rfl,?_,?_⟩
  · refine ⟨?_,rfl,by decide,rfl,?_,?_⟩
    · have f := unpackedInvariant
      exact ⟨f.heap.memory,f.heap.layout,f.heap.shape,f.heap.parentRecorded,f.heap.tailRecorded,
        f.heap.linkRecorded,f.heap.payloadRecorded,f.heap.occurrenceRecorded,f.heap.dependencies,
        rfl,f.heap.scopeRecorded⟩
    · refine ⟨unpackedInvariant.context,unpackedInvariant.heap.memory,?_,?_,?_,rfl⟩
      · constructor <;> first | rfl | decide
      · constructor <;> decide
      · simp [KnownCall.SurvivorGuard,receiverView,unpacked,unpackPost,rehome,recovered,recoverPost,
          afterExtract,closeLoan,extracted,extractPost,beforeExtract,openLoan,afterRecipient,adopted,
          recipientPost,consumeDisplacedNone,adoptCandidate,beforeAdopt,initial,Source.afterScope,
          LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,
          LiveTail.detach,LiveTail.formalEntry,KnownCall.transfer,Source.before,Source.memory,Source.roots]
    · simp [LiveTail.TerminalGuard,receiverView,unpacked,unpackPost,rehome,recovered,recoverPost,
        afterExtract,closeLoan,extracted,extractPost,beforeExtract,openLoan,afterRecipient,adopted,
        recipientPost,consumeDisplacedNone,adoptCandidate,beforeAdopt,initial,Source.afterScope,
        LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,
        LiveTail.detach,LiveTail.formalEntry,Source.before]
  · simp [ExtraTerminalGuard,unpacked,unpackPost,rehome,recovered,recoverPost,afterExtract,closeLoan,
      extracted,extractPost,beforeExtract,openLoan,afterRecipient,adopted,recipientPost,
      consumeDisplacedNone,adoptCandidate,beforeAdopt,initial]
private theorem finishedInvariant : WellFormed Source.geometry finished :=
  terminal_preserves_wellFormed actual_independent_terminal_receiver

theorem actual_second_exact_none_site : FinalApplicable Source.geometry finished := by
  refine ⟨finishedInvariant,⟨rfl,rfl,rfl,by decide,rfl,Or.inl rfl⟩,?_⟩
  simp [ChangeGuard,finished,terminalPost,unpacked,unpackPost,rehome,recovered,recoverPost,
    afterExtract,closeLoan,extracted,extractPost,beforeExtract,openLoan,afterRecipient,adopted,
    recipientPost,consumeDisplacedNone,adoptCandidate,beforeAdopt,initial]

theorem complete_adopt_extract_release_trace :
    WellFormed Source.geometry completed ∧ completed.available = false ∧ completed.holders = ∅ ∧
    completed.heap.memory.tail.phase = .released ∧ completed.heap.memory.tail.releases = 1 ∧
    completed.heap.memory.head.phase = .typed ∧ completed.heap.memory.head.releases = 0 ∧
    completed.heap.roots = initial.heap.roots :=
  ⟨final_exact_none_consumption_preserves_wellFormed actual_second_exact_none_site,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem original_tail_not_double_freed (a : F2.BindingId) (raw : Extent) :
    ¬ KnownCall.CanDeallocate completed.heap.roots completed.heap.memory a raw :=
  terminal_cannot_release_twice actual_independent_terminal_receiver a raw

/-- A read alias is compatible with write; it sees the SAME caller post-state. -/
theorem nonexclusive_alias_gets_current_post :
    currentThrough adopted {sink with write := false} = some .some ∧
    currentThrough afterRecipient {sink with write := false} = some .some := by
  constructor <;> simp [currentThrough,adopted,afterRecipient,recipientPost,consumeDisplacedNone,
    adoptCandidate,rehome,beforeAdopt,openLoan,closeLoan,initial,sink,container,Source.afterScope,LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,LiveTail.package,LiveTail.detach,LiveTail.formalEntry,Source.before]

/-- Concrete Some cannot be consumed by the recipient's one-arm None site. -/
theorem already_some_sink_rejected : ¬ Applicable Source.geometry beforeExtract extractionSink adoptPlan := by
  intro entry
  rcases entry.exactNone with bad|bad <;> cases bad

theorem unknown_sink_rejected_without_optimistic_none :
    WellFormed Source.geometry (invalidateKnowledge beforeAdopt) ∧
    ¬ Applicable Source.geometry (invalidateKnowledge beforeAdopt) sink adoptPlan :=
  ⟨forgetting_current_knowledge_preserves_wellFormed beforeInvariant,invalidated_current_knowledge_blocks_recipient⟩

theorem readonly_sink_rejected : ¬ Applicable Source.geometry beforeAdopt {sink with write := false} adoptPlan :=
  readonly_sink_blocks_recipient rfl

theorem foreign_sink_world_rejected : ¬ Applicable Source.geometry beforeAdopt {sink with world := ⟨2⟩} adoptPlan :=
  wrong_world_blocks_recipient (by decide)

theorem reused_occurrence_rejected : ¬ Applicable Source.geometry beforeAdopt sink {adoptPlan with occurrence := ⟨7⟩} :=
  historical_occurrence_cannot_be_reused (by decide)

theorem expired_sink_ref_rejected : ¬ Applicable Source.geometry initial sink adoptPlan := by
  intro entry; have active := entry.sink.2.2.2.2.1; exact Finset.notMem_empty _ active

theorem nominal_packet_cannot_certify_wrong_original_domain :
    ¬ WellFormed Source.geometry {beforeAdopt with packet := {beforeAdopt.packet with domain := ⟨1⟩}} := by
  intro wf
  have correlation := wf.correlation (by rfl)
  have wrong := correlation.2.2.2.1
  cases wrong

theorem nominal_packet_cannot_certify_wrong_original_region :
    ¬ WellFormed Source.geometry {beforeAdopt with packet := {beforeAdopt.packet with region := ⟨1⟩}} := by
  intro wf
  have correlation := wf.correlation (by rfl)
  have wrong := correlation.2.2.1
  cases wrong

theorem nominal_packet_cannot_certify_wrong_original_incarnation :
    ¬ WellFormed Source.geometry {beforeAdopt with packet := {beforeAdopt.packet with ptr := ⟨⟨2⟩,⟨1⟩⟩}} := by
  intro wf
  have correlation := wf.correlation (by rfl)
  have wrong := correlation.2.1
  cases wrong

theorem duplicate_owner_holder_breaks_invariant :
    ¬ WellFormed Source.geometry {adopted with holders := {.custody,.packet}} := by
  intro wf
  have different := noncopy_holder_cannot_duplicate wf (by rfl) (a := .custody) (b := .packet)
    (by decide) (by decide)
  cases different

theorem forgotten_owner_holder_breaks_invariant :
    ¬ WellFormed Source.geometry {adopted with holders := ∅} := by
  intro wf
  have nonempty := live_noncopy_owner_cannot_be_forgotten wf (by rfl)
  exact Finset.not_nonempty_empty nonempty

theorem after_consume_failure_cannot_hide_custody :
    ¬ WellFormed Source.geometry (refuse adopted) := by
  intro wf
  have noneTag := wf.refusal rfl
  cases noneTag

theorem final_none_consumption_needs_its_source_replacement :
    ¬ NoneOnlyLegal .callerFinal initial := by
  intro entry; cases entry.2.2.1

theorem arbitrary_one_arm_none_is_not_admitted :
    ¬ NoneOnlyLegal .elsewhere initial := elsewhere_one_arm_none_is_forbidden _

theorem recipient_old_none_consumed_without_discardability :
    NoneOnlyLegal .recipientDisplaced (adoptCandidate beforeAdopt adoptPlan) ∧
    optionDiscardable .none = false ∧ optionDiscardable .some = false ∧ adopted.oldSum = none :=
  ⟨recipient_old_result_has_exact_none_proof actual_recipient_call.2.1,rfl,rfl,rfl⟩

private def refused := refuse initial
private def refusalUnpacked := unpackPost refused unpackSupply
private def refusalFinished := terminalPost refusalUnpacked ⟨52⟩ ⟨53⟩
private def refusalBeforeExtract := openLoan refusalFinished ⟨39⟩
private def refusalExtracted := extractPost refusalBeforeExtract extractPlan
private def refusalAfterExtract := closeLoan refusalExtracted ⟨39⟩
private def refusalRecovered := recoverPost refusalAfterExtract savedSupply

private theorem refusedInvariant : WellFormed Source.geometry refused :=
  refusal_preserves_wellFormed initialInvariant rfl
private theorem refusalUnpackEntry : UnpackApplicable Source.geometry refused unpackSupply := by
  refine ⟨refusedInvariant,Or.inr (by decide),Or.inr ⟨rfl,by decide⟩,rfl,rfl,rfl,?_,?_⟩
  · refine ⟨by decide,?_,by decide,by decide⟩; constructor <;> decide
  · constructor <;> first | rfl | decide
private theorem refusalUnpackedInvariant : WellFormed Source.geometry refusalUnpacked :=
  unpacking_preserves_wellFormed refusalUnpackEntry
private theorem refusalTerminalEntry : TerminalApplicable Source.geometry refusalUnpacked ⟨52⟩ ⟨53⟩ := by
  refine ⟨refusalUnpackedInvariant,by decide,Or.inr rfl,rfl,rfl,rfl,?_,?_⟩
  · have f := refusalUnpackedInvariant
    refine ⟨⟨f.heap.memory,f.heap.layout,f.heap.shape,f.heap.parentRecorded,f.heap.tailRecorded,
      f.heap.linkRecorded,f.heap.payloadRecorded,f.heap.occurrenceRecorded,f.heap.dependencies,rfl,f.heap.scopeRecorded⟩,
      rfl,by decide,rfl,?_,?_⟩
    · refine ⟨f.context,f.heap.memory,?_,?_,?_ ,rfl⟩
      · constructor <;> first | rfl | decide
      · constructor <;> decide
      · change ∀ f, (f ∈ (∅ : Finset F0.Fact) ∨ f ∈ (∅ : Finset F0.Fact)) → _
        simp
    · change ∀ d ∈ (∅ : Finset LiveTail.Dependency), _
      simp
  · change ∀ d ∈ (∅ : Finset LiveTail.Dependency), _
    simp
private theorem refusalFinishedInvariant : WellFormed Source.geometry refusalFinished :=
  terminal_preserves_wellFormed refusalTerminalEntry
private theorem refusalExtractEntry : ExtractApplicable Source.geometry refusalBeforeExtract extractionSink extractPlan := by
  refine ⟨opening_local_loan_preserves_wellFormed refusalFinishedInvariant _,?_,rfl,Or.inr rfl,
    Or.inr rfl,(fun _ => rfl),?_,by decide,by decide,?_,?_,?_⟩
  · constructor <;> first | rfl | decide
  · refine ⟨by decide,?_,by decide,by decide⟩; constructor <;> decide
  · intro impossible; cases impossible
  · change ∀ d ∈ (∅ : Finset LiveTail.Dependency), _; simp
  · change LiveTail.Dependency.scope ⟨39⟩ ∉ (∅ : Finset LiveTail.Dependency) ∧
      LiveTail.Dependency.scope ⟨39⟩ ∉ (∅ : Finset LiveTail.Dependency)
    simp
private theorem refusalExtractedInvariant : WellFormed Source.geometry refusalExtracted :=
  extraction_preserves_wellFormed refusalExtractEntry
private theorem refusalAfterExtractInvariant : WellFormed Source.geometry refusalAfterExtract := by
  apply closing_local_loan_preserves_wellFormed refusalExtractedInvariant
  change LiveTail.Dependency.scope ⟨39⟩ ∉ (∅ : Finset LiveTail.Dependency) ∧
      LiveTail.Dependency.scope ⟨39⟩ ∉ (∅ : Finset LiveTail.Dependency)
  simp
private theorem refusalRecoverEntry : RecoverApplicable Source.geometry refusalAfterExtract savedSupply := by
  refine ⟨refusalAfterExtractInvariant,⟨⟨.none,.extraction,.initializedNone ⟨200⟩,⟨200⟩⟩,rfl,rfl⟩,
    by decide,rfl,rfl,?_,?_⟩
  · refine ⟨by decide,?_,by decide,by decide⟩; constructor <;> decide
  · rintro ⟨old,present,someTag⟩
    have tag : old.tag = .none := by cases Option.some.inj present; rfl
    rw [tag] at someTag; cases someTag
private theorem refusalRecoveredInvariant : WellFormed Source.geometry refusalRecovered :=
  recovery_preserves_wellFormed refusalRecoverEntry
private theorem refusalFinalEntry : FinalApplicable Source.geometry refusalRecovered := by
  refine ⟨refusalRecoveredInvariant,⟨rfl,rfl,rfl,by decide,rfl,Or.inr ⟨rfl,rfl⟩⟩,?_⟩
  change ∀ d ∈ (∅ : Finset LiveTail.Dependency), _; simp

theorem refusal_before_consume_preserves_owner_then_releases :
    refused.holders = initial.holders ∧ refused.packet = initial.packet ∧
    refused.heap = initial.heap ∧
    WellFormed Source.geometry (consumeFinalNone refusalRecovered) ∧
    refusalRecovered.holders = ∅ ∧ refusalRecovered.heap.memory.tail.releases = 1 ∧
    refusalRecovered.heap.memory.head.releases = 0 ∧ refusalRecovered.usedOccurrences = initial.usedOccurrences :=
  ⟨rfl,rfl,rfl,final_exact_none_consumption_preserves_wellFormed refusalFinalEntry,rfl,rfl,rfl,rfl⟩

private def withExtra (s : State) (deps : Finset LiveTail.Dependency) : State :=
  {s with extraDependencies := deps}
private theorem withExtraInvariant {g s deps} (wf : WellFormed g s)
    (live : DependenciesValid (withExtra s deps)) : WellFormed g (withExtra s deps) := by
  have f := wf.toOwnerFrame
  exact ⟨⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
    f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩,
    wf.currentRecorded,wf.occurrenceRecorded,wf.payloadRecorded,wf.knowledge,wf.shape,
    wf.custody,wf.displaced,live,wf.refusal⟩

private def escaping := withExtra beforeAdopt {.scope ⟨31⟩}
private theorem escapingInvariant : WellFormed Source.geometry escaping := by
  apply withExtraInvariant beforeInvariant
  intro dep mem
  have same : dep = .scope ⟨31⟩ := Finset.mem_singleton.mp mem
  subst dep; change (⟨31⟩ : F2.BindingId) ∈ beforeAdopt.heap.scopes ∪ beforeAdopt.loans
  decide

theorem live_sink_scope_cannot_escape_recipient :
    WellFormed Source.geometry escaping ∧ ¬ Applicable Source.geometry escaping sink adoptPlan :=
  ⟨escapingInvariant,escaped_sink_scope_blocks_recipient (by decide)⟩

private def observed := withExtra beforeExtract {.memory (.occurrence ⟨50⟩)}
private theorem observedInvariant : WellFormed Source.geometry observed := by
  apply withExtraInvariant beforeExtractInvariant
  intro dep mem
  have same : dep = .memory (.occurrence ⟨50⟩) := Finset.mem_singleton.mp mem
  subst dep
  exact Or.inr ⟨rfl,rfl⟩

theorem occurrence_observer_blocks_delayed_extract :
    WellFormed Source.geometry observed ∧ ¬ ExtractApplicable Source.geometry observed extractionSink extractPlan :=
  ⟨observedInvariant,any_surviving_sink_occurrence_blocks_extract (by decide) rfl⟩

/-- Removing ONLY the dependency guard still moves the owner, but launders a
survivor's dependency on the ended conditional occurrence. -/
theorem unchecked_extract_keeps_heap_but_breaks_dependency :
    (extractPost observed extractPlan).heap.roots = observed.heap.roots ∧
    (extractPost observed extractPlan).heap.memory.tail.phase = .typed ∧
    (extractPost observed extractPlan).holders = {.displaced} ∧
    ¬ DependenciesValid (extractPost observed extractPlan) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro valid
  have live := valid (.memory (.occurrence ⟨50⟩)) (by decide)
  rcases live with heap|sum
  · have old : Source.afterScope.link.occurrence = some ⟨50⟩ := heap.2
    cases old
  · have old : (none : Option F1.Conditional.OccurrenceId) = some ⟨50⟩ := sum.2
    cases old

theorem erased_source_knowledge_cannot_supply_displaced_none_match :
    ¬ NoneOnlyLegal .recipientDisplaced
      {initial with oldSum := some ⟨.none,.adoption,.unknown,⟨200⟩⟩} := by
  rintro ⟨old,present,_,_,proof⟩
  cases Option.some.inj present
  exact unknown_current_cannot_prove_exact_none _ proof

theorem may_some_cannot_mint_zero_owner_proof :
    ¬ SourceNone .maySome initial.currentFact := may_some_cannot_prove_exact_none _

theorem non_caller_owned_sink_rejected :
    ¬ Applicable Source.geometry {initial with container := {container with callerOwned := false}}
      {sink with root := {container with callerOwned := false}} adoptPlan := by
  intro entry; cases entry.sink.2.2.1

theorem recipient_formal_and_donor_unavailable_after_return :
    adopted.heap.memory.carrier .tailAllocation ≠ some ⟨11⟩ ∧
    adopted.heap.memory.carrier .tailDomain ≠ some ⟨12⟩ ∧
    adopted.heap.memory.carrier .tailAllocation ≠ some adoptPlan.formal.allocation ∧
    adopted.heap.memory.carrier .tailDomain ≠ some adoptPlan.formal.domain ∧
    adoptPlan.formal.allocation ∈ adopted.heap.memory.usedBindings ∧
    adoptPlan.formal.domain ∈ adopted.heap.memory.usedBindings := by decide

theorem saved_packet_cannot_be_reused_after_unpack :
    Holder.saved ∉ unpacked.holders ∧ Holder.unpacked ∈ unpacked.holders ∧
    ¬ UnpackApplicable Source.geometry unpacked unpackSupply := by
  refine ⟨by decide,by decide,?_⟩
  intro entry
  rcases entry.present with bad|bad <;> cases Finset.mem_singleton.mp bad

private def swapContext (c : KnownCall.Context) : KnownCall.Context :=
  {c with head := c.tail,tail := c.head}
private def swapMemory (s : KnownCall.State) : KnownCall.State :=
  {s with head := s.tail,tail := s.head,carrier := fun r => match r with
    | .headAllocation => s.carrier .tailAllocation
    | .headDomain => s.carrier .tailDomain
    | .tailAllocation => s.carrier .headAllocation
    | .tailDomain => s.carrier .headDomain}
private def headView := swapMemory completed.heap.memory
private def cleaned := swapMemory (KnownCall.receiver headView)

theorem head_cleanup_has_its_own_primitive_guards :
    KnownCall.CanEnd (swapContext completed.heap.roots) headView ⟨2⟩ ∧
    KnownCall.CanEraseSlot (KnownCall.endRoot headView) ∧
    KnownCall.CanFinalize (swapContext completed.heap.roots)
      (KnownCall.eraseSlot (KnownCall.endRoot headView)) ⟨2⟩ ∧
    KnownCall.CanDeallocate (swapContext completed.heap.roots)
      (KnownCall.finalize (KnownCall.eraseSlot (KnownCall.endRoot headView)))
      ⟨1⟩ initial.heap.roots.head.extent := by
  refine ⟨?_,rfl,?_,?_⟩
  · dsimp [KnownCall.CanEnd,swapContext,headView,swapMemory,completed,consumeFinalNone,finished,
      terminalPost,LiveTail.terminalPost,receiverView,KnownCall.callPost,KnownCall.receiver,
      KnownCall.deallocate,KnownCall.finalize,KnownCall.eraseSlot,KnownCall.endRoot,unpacked,unpackPost,
      recovered,recoverPost,afterExtract,closeLoan,extracted,extractPost,beforeExtract,openLoan,
      afterRecipient,adopted,recipientPost,consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,
      initial,Source.afterScope,LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,
      LiveTail.package,LiveTail.detach,LiveTail.formalEntry,KnownCall.transfer,Source.before,Source.memory,Source.roots]
    decide
  · refine ⟨rfl,rfl,rfl,Finset.notMem_empty _,?_,?_⟩
    · intro o governing
      rcases governing with ⟨i,typed,_,_⟩
      cases i <;> cases typed
    · intro f member
      change f ∈ (∅ : Finset F0.Fact) ∨ f ∈ (∅ : Finset F0.Fact) at member
      simp at member
  · dsimp [KnownCall.CanDeallocate,swapContext,headView,swapMemory,completed,consumeFinalNone,finished,
      terminalPost,LiveTail.terminalPost,receiverView,KnownCall.callPost,KnownCall.receiver,
      KnownCall.deallocate,KnownCall.finalize,KnownCall.eraseSlot,KnownCall.endRoot,unpacked,unpackPost,
      recovered,recoverPost,afterExtract,closeLoan,extracted,extractPost,beforeExtract,openLoan,
      afterRecipient,adopted,recipientPost,consumeDisplacedNone,adoptCandidate,rehome,beforeAdopt,
      initial,Source.afterScope,LiveTail.closeHeadScope,Source.returned,LiveTail.producerPost,
      LiveTail.package,LiveTail.detach,LiveTail.formalEntry,KnownCall.transfer,Source.before,Source.memory,Source.roots]
    decide

theorem two_original_roots_released_once_after_durable_custody :
    cleaned.head.phase = .released ∧ cleaned.tail.phase = .released ∧
    cleaned.head.releases = 1 ∧ cleaned.tail.releases = 1 ∧
    (∀ r, cleaned.carrier r = none) ∧
    KnownCall.responsibility completed.heap.roots cleaned .head = none ∧
    KnownCall.responsibility completed.heap.roots cleaned .tail = none := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl⟩
  intro r; cases r <;> rfl

/-- Optional successful backing snapshots for the two failure worlds. An absent
allocation has NO cell and NO owners; it is not a fabricated "released root".
No allocator/source checker is asserted by these closed branch controls. -/
private structure FailureSnapshot where
  cell : Option KnownCall.Cell
  allocation : Option F2.BindingId
  domain : Option F2.BindingId
private def FailureInvariant (s : FailureSnapshot) : Prop :=
  match s.cell with
  | none => s.allocation = none ∧ s.domain = none
  | some c =>
    (s.allocation.isSome = true ↔ c.phase ≠ .released) ∧
    (s.domain.isSome = true ↔ c.domainLive = true) ∧
    c.releases = (if c.phase = .released then 1 else 0) ∧
    (c.phase = .typed → c.domainLive = true)
private def noBacking : FailureSnapshot := ⟨none,none,none⟩
private def headOnly : FailureSnapshot := ⟨some ⟨.typed,true,0⟩,some ⟨1⟩,some ⟨2⟩⟩
/-- The unused head component is just padding for the existing tail-targeted
primitive signatures. Only the target tail component represents the ONE head
backing in this failure branch; no KnownCall global invariant is claimed. -/
private def singleHeadView : KnownCall.State where
  head := ⟨.released,false,0⟩
  tail := ⟨.typed,true,0⟩
  carrier := fun r => match r with
    | .tailAllocation => headOnly.allocation | .tailDomain => headOnly.domain | _ => none
  usedBindings := {⟨1⟩,⟨2⟩}
  externalDependencies := ∅
  blockers := ∅
  issuedPtrs := ∅
  readableRegions := ∅
  platformReady := true
private def singleHeadReleased : FailureSnapshot :=
  ⟨some (KnownCall.receiver singleHeadView).tail,
    (KnownCall.receiver singleHeadView).carrier .tailAllocation,
    (KnownCall.receiver singleHeadView).carrier .tailDomain⟩

theorem zero_allocation_failure_has_no_owner_or_release :
    FailureInvariant noBacking ∧ noBacking.cell = none ∧
    noBacking.allocation = none ∧ noBacking.domain = none := ⟨⟨rfl,rfl⟩,rfl,rfl,rfl⟩

theorem one_allocation_failure_has_guarded_exact_head_cleanup :
    FailureInvariant headOnly ∧
    KnownCall.CanEnd (swapContext Source.roots) singleHeadView ⟨2⟩ ∧
    KnownCall.CanEraseSlot (KnownCall.endRoot singleHeadView) ∧
    KnownCall.CanFinalize (swapContext Source.roots)
      (KnownCall.eraseSlot (KnownCall.endRoot singleHeadView)) ⟨2⟩ ∧
    KnownCall.CanDeallocate (swapContext Source.roots)
      (KnownCall.finalize (KnownCall.eraseSlot (KnownCall.endRoot singleHeadView))) ⟨1⟩ Source.roots.head.extent ∧
    FailureInvariant singleHeadReleased ∧
    singleHeadReleased.cell = some ⟨.released,false,1⟩ ∧
    singleHeadReleased.allocation = none ∧ singleHeadReleased.domain = none := by
  refine ⟨?_,?_,rfl,?_,?_,?_,rfl,rfl,rfl⟩
  · simp [FailureInvariant,headOnly]
  · dsimp [KnownCall.CanEnd,swapContext,Source.roots,singleHeadView,headOnly]; decide
  · refine ⟨rfl,rfl,rfl,Finset.notMem_empty _,?_,?_⟩
    · intro o governing; rcases governing with ⟨i,typed,_,_⟩; cases i <;> cases typed
    · intro f member
      change f ∈ (∅ : Finset F0.Fact) ∨ f ∈ (∅ : Finset F0.Fact) at member; simp at member
  · dsimp [KnownCall.CanDeallocate,swapContext,Source.roots,KnownCall.finalize,
      KnownCall.eraseSlot,KnownCall.endRoot,singleHeadView,headOnly]; decide
  · simp [FailureInvariant,singleHeadReleased,KnownCall.receiver,KnownCall.deallocate,
      KnownCall.finalize,KnownCall.eraseSlot,KnownCall.endRoot,singleHeadView,headOnly]

private def tailObserved := withExtra beforeAdopt {.memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩))}
private theorem tailObservedInvariant : WellFormed Source.geometry tailObserved := by
  apply withExtraInvariant beforeInvariant
  intro dep mem
  have same : dep = .memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩)) := Finset.mem_singleton.mp mem
  subst dep
  exact Or.inl (Or.inl ⟨.tail,rfl,rfl,rfl⟩)

private theorem tailObservedEntry : Applicable Source.geometry tailObserved sink adoptPlan := by
  have e := actual_recipient_call.2.1
  refine ⟨tailObservedInvariant,e.packet,e.oldAbsent,e.pending,e.site,e.exactNone,e.sink,⟨e.ready.live,e.ready.allocationScope,e.ready.domainScope⟩,e.fresh,
    e.heapFresh,?_,?_,?_,e.headEnded,?_⟩
  · simp [ChangeGuard,tailObserved,withExtra,EndsAtChange,beforeAdopt,openLoan,initial,container]
  · exact ⟨by decide,e.sinkScope.2⟩
  · exact ⟨by decide,e.frameScope.2⟩
  · exact ⟨by decide,e.headEscape.2⟩

/-- A live heap observer is compatible with custody transfer; it independently
blocks the later lifetime-ending terminal call. No transfer=EndRoot shortcut. -/
theorem live_tail_dependency_survives_recipient_but_blocks_terminal :
    RecipientCall Source.geometry selectedBody tailObserved sink adoptPlan (recipientPost tailObserved adoptPlan) ∧
    WellFormed Source.geometry (recipientPost tailObserved adoptPlan) ∧
    ¬ ExtraTerminalGuard (recipientPost tailObserved adoptPlan) := by
  refine ⟨⟨rfl,tailObservedEntry,rfl⟩,recipient_preserves_wellFormed ⟨rfl,tailObservedEntry,rfl⟩,?_⟩
  intro guard
  have safe := guard (.memory (.fixed (.valueFact ⟨2⟩ ⟨2⟩))) (by decide)
    (.fixed (.valueFact ⟨2⟩ ⟨2⟩)) rfl
  exact safe.1 rfl

/-- Root-ending blockers are not owner-value borrow blockers. The recipient
moves A/D without ending O_t; terminal CanEnd still refuses the live root ref. -/
private def rootBorrowed : State :=
  {beforeAdopt with heap := {(beforeAdopt.heap) with memory := {(beforeAdopt.heap.memory) with
    blockers := {.root ⟨2⟩}}}}
private theorem rootBorrowedInvariant : WellFormed Source.geometry rootBorrowed := by
  have f := beforeInvariant.toOwnerFrame
  have k := f.heap.memory
  have heap : LiveTail.WellFormed rootBorrowed.heap :=
    ⟨⟨k.allocation,k.domain,k.typedDomain,k.slotDomain,k.releasedDomain,k.releaseCount,k.recorded,
      k.unique,k.dependencies⟩,f.heap.layout,f.heap.shape,f.heap.parentRecorded,f.heap.tailRecorded,
      f.heap.linkRecorded,f.heap.payloadRecorded,f.heap.occurrenceRecorded,f.heap.dependencies,
      f.heap.package,f.heap.scopeRecorded⟩
  exact ⟨⟨heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
    f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩,
    beforeInvariant.currentRecorded,beforeInvariant.occurrenceRecorded,beforeInvariant.payloadRecorded,
    beforeInvariant.knowledge,beforeInvariant.shape,beforeInvariant.custody,beforeInvariant.displaced,
    beforeInvariant.dependencies,beforeInvariant.refusal⟩
private theorem rootBorrowedEntry : Applicable Source.geometry rootBorrowed sink adoptPlan := by
  have e := actual_recipient_call.2.1
  refine ⟨rootBorrowedInvariant,e.packet,e.oldAbsent,e.pending,e.site,e.exactNone,e.sink,?_,?_,e.heapFresh,
    e.change,e.sinkScope,e.frameScope,e.headEnded,e.headEscape⟩
  · constructor <;> first | rfl | decide
  · refine ⟨e.fresh.1,e.fresh.2.1,?_,e.fresh.2.2.2⟩
    intro b _; simp [rootBorrowed]

theorem recipient_requires_no_heap_lifetime_ending_authority :
    RecipientCall Source.geometry selectedBody rootBorrowed sink adoptPlan (recipientPost rootBorrowed adoptPlan) ∧
    ¬ KnownCall.CanEnd rootBorrowed.heap.roots rootBorrowed.heap.memory rootBorrowed.packet.domainField := by
  refine ⟨⟨rfl,rootBorrowedEntry,rfl⟩,?_⟩
  intro ending
  exact ending.2.2.1 (by decide)

theorem stale_recipient_loan_cannot_write_caller_after_return :
    ¬ SinkValid afterRecipient sink := ended_loan_never_grants_write_permission (by decide)

/-- The base carrier table also rejects a copied ptr with a missing original
owner field, independently of the holder-support duplicate/loss controls. -/
theorem copied_ptr_cannot_replace_missing_allocation_owner :
    ¬ WellFormed Source.geometry
      {beforeAdopt with heap := {(beforeAdopt.heap) with memory := {(beforeAdopt.heap.memory) with
        carrier := fun r => if r = .tailAllocation then none else beforeAdopt.heap.memory.carrier r}}} := by
  intro wf
  have corr := wf.correlation (by rfl)
  have present := corr.2.2.2.2.2.2.1
  cases present


theorem two_distinct_fresh_caller_loans :
    LoanStep Source.geometry initial ⟨31⟩ beforeAdopt ∧
    LoanStep Source.geometry afterRecipient ⟨39⟩ beforeExtract ∧
    (⟨31⟩ : F2.BindingId) ≠ ⟨39⟩ :=
  ⟨⟨initialInvariant,by decide,rfl⟩,⟨afterRecipientInvariant,by decide,rfl⟩,by decide⟩

theorem stale_loan_cannot_be_revived_by_reusing_scope_id :
    ¬ LoanStep Source.geometry afterRecipient ⟨31⟩ (openLoan afterRecipient ⟨31⟩) :=
  historical_loan_scope_cannot_be_reopened (by decide)


private def refusalHeadView := swapMemory (consumeFinalNone refusalRecovered).heap.memory
private def refusalCleaned := swapMemory (KnownCall.receiver refusalHeadView)

theorem refusal_independent_head_cleanup_releases_both_once :
    KnownCall.CanEnd (swapContext completed.heap.roots) refusalHeadView ⟨2⟩ ∧
    KnownCall.CanEraseSlot (KnownCall.endRoot refusalHeadView) ∧
    KnownCall.CanFinalize (swapContext completed.heap.roots)
      (KnownCall.eraseSlot (KnownCall.endRoot refusalHeadView)) ⟨2⟩ ∧
    KnownCall.CanDeallocate (swapContext completed.heap.roots)
      (KnownCall.finalize (KnownCall.eraseSlot (KnownCall.endRoot refusalHeadView)))
      ⟨1⟩ initial.heap.roots.head.extent ∧
    refusalCleaned.head.releases = 1 ∧ refusalCleaned.tail.releases = 1 ∧
    (∀ r, refusalCleaned.carrier r = none) := by
  have guards := head_cleanup_has_its_own_primitive_guards
  refine ⟨guards.1,guards.2.1,guards.2.2.1,guards.2.2.2,rfl,rfl,?_⟩
  intro r; cases r <;> rfl

end
end NewLang.Adjunct.Custody.Counterexample
