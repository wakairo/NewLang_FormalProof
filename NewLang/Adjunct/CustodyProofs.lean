import NewLang.Adjunct.Custody
import Mathlib.Data.List.Nodup

namespace NewLang.Adjunct.Custody
open F0 F1.Backing F1.Occupancy
noncomputable section

private theorem history_heap {s : LiveTail.State} {u : Finset F2.BindingId}
    (wf : LiveTail.WellFormed s) (stage : s.stage = .consumed) (bundle : s.bundle = none)
    (more : s.memory.usedBindings ⊆ u) :
    LiveTail.WellFormed {s with memory := {s.memory with usedBindings := u}} := by
  have k := wf.memory
  refine ⟨⟨k.allocation,k.domain,k.typedDomain,k.slotDomain,k.releasedDomain,k.releaseCount,
    (fun r b h => more (k.recorded r b h)),k.unique,k.dependencies⟩,
    wf.layout,wf.shape,wf.parentRecorded,wf.tailRecorded,wf.linkRecorded,wf.payloadRecorded,
    wf.occurrenceRecorded,wf.dependencies,?_,(fun b h => more (wf.scopeRecorded b h))⟩
  simp [LiveTail.PackageShape,stage,bundle]

private theorem transfer_live_preserves_accounting {c : KnownCall.Context} {s : KnownCall.State} {a d : F2.BindingId}
    (wf : KnownCall.WellFormed c s) (live : s.tail.phase = .typed) (fresh : KnownCall.FreshParameters s a d) :
    KnownCall.WellFormed c (KnownCall.transfer s a d) := by
  constructor
  · intro i; cases i with
    | head => exact wf.allocation .head
    | tail => simp [KnownCall.transfer,KnownCall.allocationRole,KnownCall.State.cell,live]
  · intro i; cases i with
    | head => exact wf.domain .head
    | tail => simpa [KnownCall.transfer,KnownCall.domainRole,KnownCall.State.cell] using wf.typedDomain .tail live
  · exact wf.typedDomain
  · exact wf.slotDomain
  · exact wf.releasedDomain
  · exact wf.releaseCount
  · intro r b present; cases r with
    | headAllocation => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.recorded _ _ present))
    | headDomain => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.recorded _ _ present))
    | tailAllocation => have eq := Option.some.inj present; subst b; simp [KnownCall.transfer]
    | tailDomain => have eq := Option.some.inj present; subst b; simp [KnownCall.transfer]
  · intro r q b rb qb
    have oldA : ∀ r, s.carrier r ≠ some a := by
      intro r present; exact fresh.allocationFresh (wf.recorded r a present)
    have oldD : ∀ r, s.carrier r ≠ some d := by
      intro r present; exact fresh.domainFresh (wf.recorded r d present)
    cases r <;> cases q <;>
      simp only [KnownCall.transfer] at rb qb <;>
      first | rfl | exact wf.unique _ _ _ rb qb |
        (have eq := Option.some.inj rb; subst b; exact False.elim (oldA _ qb)) |
        (have eq := Option.some.inj qb; subst b; exact False.elim (oldA _ rb)) |
        (have eq := Option.some.inj rb; subst b; exact False.elim (oldD _ qb)) |
        (have eq := Option.some.inj qb; subst b; exact False.elim (oldD _ rb)) |
        exact False.elim (fresh.distinct ((Option.some.inj rb).trans (Option.some.inj qb).symm)) |
        exact False.elim (fresh.distinct ((Option.some.inj qb).trans (Option.some.inj rb).symm))
  · exact wf.dependencies

private theorem rehome_heap {g s donor target p} (wf : OwnerFrame g s)
    (ready : ReadyPacket s) (fresh : p.fresh s) : LiveTail.WellFormed (rehome s donor target p).heap := by
  have k := transfer_live_preserves_accounting wf.heap.memory ready.live fresh.2.1
  refine ⟨⟨k.allocation,k.domain,k.typedDomain,k.slotDomain,k.releasedDomain,k.releaseCount,
    (fun r b h => Finset.mem_insert_of_mem (k.recorded r b h)),k.unique,k.dependencies⟩,
    wf.heap.layout,wf.heap.shape,wf.heap.parentRecorded,wf.heap.tailRecorded,wf.heap.linkRecorded,
    wf.heap.payloadRecorded,wf.heap.occurrenceRecorded,wf.heap.dependencies,rfl,?_⟩
  intro b live
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (wf.heap.scopeRecorded b live)))

private theorem singleton_holder {g s donor} (wf : OwnerFrame g s) (ready : ReadyPacket s)
    (present : donor ∈ s.holders) : s.holders = {donor} := by
  rcases wf.cover ready.live with ⟨h,eq⟩
  rw [eq] at present
  have same : donor = h := Finset.mem_singleton.mp present
  subst h; exact eq

private theorem rehome_frame {g s donor target p} (wf : OwnerFrame g s)
    (ready : ReadyPacket s) (present : donor ∈ s.holders) (fresh : p.fresh s) :
    OwnerFrame g (rehome s donor target p) := by
  have only := singleton_holder wf ready present
  have postOnly : (rehome s donor target p).holders = {target} := by simp [rehome,only]
  have corr := wf.correlation ready.live
  refine ⟨rehome_heap wf ready fresh,⟨rfl,rfl⟩,wf.context,wf.approved,wf.roots,wf.world,?_,
    wf.localDistinct,?_,(fun _ => ⟨target,postOnly⟩),?_,?_,?_,?_⟩
  · rcases wf.original with ⟨b,old,world,ptr,region,domain,deps⟩
    exact ⟨b,old,world,ptr,region,domain,deps⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem wf.localRecorded))
  · intro released; change s.heap.memory.tail.phase = .released at released; have live := ready.live; rw [live] at released; cases released
  · intro _
    exact ⟨corr.1,corr.2.1,corr.2.2.1,corr.2.2.2.1,corr.2.2.2.2.1,
      corr.2.2.2.2.2.1,rfl,rfl,corr.2.2.2.2.2.2.2.2⟩
  · intro _; exact Finset.mem_insert_self _ _
  · intro _ r owner
    cases r with
    | headAllocation =>
      exact fresh.1 (wf.heap.memory.recorded .headAllocation p.placement owner)
    | headDomain =>
      exact fresh.1 (wf.heap.memory.recorded .headDomain p.placement owner)
    | tailAllocation => exact fresh.2.2.1 (Option.some.inj owner).symm
    | tailDomain => exact fresh.2.2.2 (Option.some.inj owner).symm

private theorem changed_extra {s post} (heapFacts : ∀ f, LiveTail.FactLive s.heap f → LiveTail.FactLive post.heap f)
    (scopeMore : s.heap.scopes ∪ s.loans ⊆ post.heap.scopes ∪ post.loans)
    (extra : post.extraDependencies = s.extraDependencies)
    (wf : DependenciesValid s) (guard : ChangeGuard s) : DependenciesValid post := by
  intro dep member
  rw [extra] at member
  have live := wf dep member
  cases dep with
  | scope b => exact scopeMore live
  | memory f =>
    rcases live with oldHeap|oldLocal
    · exact Or.inl (heapFacts f oldHeap)
    · have safe := guard _ member f rfl
      cases f with
      | fixed fact =>
        cases fact with
        | valueFact p vf => exact False.elim (safe ⟨oldLocal.2.1,oldLocal.2.2⟩)
        | domainLive d => exact False.elim oldLocal
      | occurrence o => exact False.elim (safe oldLocal.2)
      | payloadValue o vf => exact False.elim (safe oldLocal.2)

private theorem supply_from_plan {s p} (fresh : AdoptFresh s p) {i j k : Nat}
    (hi : i < p.bindings.length) (hj : j < p.bindings.length) (hk : k < p.bindings.length)
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    (Supply.mk p.bindings[i] p.bindings[j] p.bindings[k]).fresh s := by
  refine ⟨fresh.2.1 _ (List.getElem_mem hi),
    ⟨fresh.2.1 _ (List.getElem_mem hj),fresh.2.1 _ (List.getElem_mem hk),?_,
      (fresh.2.2.1 _ (List.getElem_mem hj)).1,(fresh.2.2.1 _ (List.getElem_mem hk)).2⟩,?_,?_⟩
  · exact fun eq => jk (fresh.1.getElem_inj_iff.mp eq)
  · exact fun eq => ij (fresh.1.getElem_inj_iff.mp eq)
  · exact fun eq => ik (fresh.1.getElem_inj_iff.mp eq)

theorem recipient_formal_supply_fresh {s p} (fresh : AdoptFresh s p) : p.formal.fresh s :=
  supply_from_plan fresh (i := 1) (j := 2) (k := 3)
    (by simp [AdoptPlan.bindings]) (by simp [AdoptPlan.bindings]) (by simp [AdoptPlan.bindings])
    (by decide) (by decide) (by decide)

theorem recipient_payload_supply_fresh {s p} (fresh : AdoptFresh s p) : p.payload.fresh s :=
  supply_from_plan fresh (i := 4) (j := 5) (k := 6)
    (by simp [AdoptPlan.bindings]) (by simp [AdoptPlan.bindings]) (by simp [AdoptPlan.bindings])
    (by decide) (by decide) (by decide)

private theorem actual_none {g s r p} (call : Applicable g s r p) :
    s.available = true ∧ s.tag = .none := by
  rcases call.exactNone with init|replaced
  · have sound := call.pre.knowledge; simp only [KnowledgeSound,init] at sound; exact ⟨sound.1,sound.2.1⟩
  · have sound := call.pre.knowledge; simp only [KnowledgeSound,replaced] at sound; exact ⟨sound.1,sound.2.1⟩

theorem recipient_old_result_has_exact_none_proof {g s r p} (call : Applicable g s r p) :
    NoneOnlyLegal .recipientDisplaced (adoptCandidate s p) :=
  ⟨⟨s.tag,.adoption,s.knowledge,s.currentFact⟩,rfl,rfl,(actual_none call).2,call.exactNone⟩

theorem option_capabilities_are_static (tag : Tag) : optionCopyable tag = false ∧ optionDiscardable tag = false :=
  ⟨rfl,rfl⟩

/-- No post invariant premise; complete atomic recipient proof from actual entry. -/
theorem recipient_preserves_wellFormed {g body s r p post}
    (step : RecipientCall g body s r p post) : WellFormed g post := by
  rcases step with ⟨_,call,rfl⟩
  have moved := rehome_frame (target := .custody) call.pre.toOwnerFrame call.ready call.packet (recipient_payload_supply_fresh call.fresh)
  have only : (recipientPost s p).holders = {.custody} := by
    simp [recipientPost,consumeDisplacedNone,adoptCandidate,rehome,singleton_holder call.pre.toOwnerFrame call.ready call.packet]
  have core : OwnerFrame g (recipientPost s p) := by
    refine ⟨?_,moved.envelope,moved.context,moved.approved,moved.roots,moved.world,moved.original,
      moved.localDistinct,Finset.mem_union_left _ moved.localRecorded,
      (fun _ => ⟨.custody,only⟩),moved.released,moved.correlation,?_,moved.placementSeparate⟩
    · exact history_heap moved.heap rfl rfl (Finset.subset_union_left)
    · intro live; exact Finset.mem_union_left _ (moved.placementRecorded live)
  refine ⟨core,?_,?_,?_,trivial,⟨by simp [recipientPost,consumeDisplacedNone,adoptCandidate],
    by simp [recipientPost,consumeDisplacedNone,adoptCandidate]⟩,?_,?_,?_,?_⟩
  · exact Finset.mem_insert_self _ _
  · intro o eq; change some p.occurrence = some o at eq; cases Option.some.inj eq
    exact Finset.mem_insert_self _ _
  · intro vf eq; change some p.payloadFact = some vf at eq; cases Option.some.inj eq
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · change (Holder.custody ∈ (recipientPost s p).holders ↔ s.available = true ∧ Tag.some = .some)
    rw [only]; simp [(actual_none call).1]
  · change (Holder.displaced ∈ (recipientPost s p).holders ↔ ∃ o, (none : Option OldSum) = some o ∧ o.tag = .some)
    rw [only]; simp
  · apply changed_extra (s := s) (post := recipientPost s p) (fun _ live => live) (by intro b mem; exact mem) rfl
      call.pre.dependencies call.change
  · intro bad; cases bad

/-- A conditional definition proof never supplies caller identities/current None. -/
def ConditionalDefinition (g : Geometry) (body : List Command) : Prop :=
  DefinitionChecked body ∧ ∀ s r p, Applicable g s r p →
    WellFormed g (recipientPost s p)

theorem recipient_definition_is_conditional (g : Geometry) : ConditionalDefinition g selectedBody :=
  ⟨rfl,fun _ _ _ entry => recipient_preserves_wellFormed ⟨rfl,entry,rfl⟩⟩

theorem recipient_preserves_original_heap {g body s r p post}
    (step : RecipientCall g body s r p post) :
    post.heap.roots = s.heap.roots ∧ post.heap.memory.head = s.heap.memory.head ∧
    post.heap.memory.tail = s.heap.memory.tail ∧ post.container = s.container ∧
    post.packet.ptr = s.packet.ptr ∧ post.packet.region = s.packet.region ∧
    post.packet.domain = s.packet.domain ∧ post.packet.dependencies = s.packet.dependencies := by
  rw [step.2.2]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem recipient_creates_only_a_conditional_occurrence {g body s r p post}
    (step : RecipientCall g body s r p post) :
    p.occurrence ∉ s.usedOccurrences ∧ post.occurrence = some p.occurrence ∧
    p.occurrence ∈ post.usedOccurrences ∧ s.usedOccurrences ⊆ post.usedOccurrences ∧
    post.container.incarnation = s.container.incarnation ∧
    post.heap.roots.tail.incarnation = s.heap.roots.tail.incarnation := by
  rcases step with ⟨_,entry,rfl⟩
  exact ⟨entry.fresh.2.2.2.2.2.2,rfl,Finset.mem_insert_self _ _,Finset.subset_insert _ _,rfl,rfl⟩

theorem recipient_transfers_exactly_one_owner {g body s r p post}
    (step : RecipientCall g body s r p post) :
    post.holders = {.custody} ∧ Holder.packet ∉ post.holders ∧ Holder.formal ∉ post.holders ∧
    post.tag = .some ∧ post.oldSum = none := by
  rcases step with ⟨_,call,rfl⟩
  have only := singleton_holder call.pre.toOwnerFrame call.ready call.packet
  simp [recipientPost,consumeDisplacedNone,adoptCandidate,rehome,only]

theorem recipient_consumes_original_donor_bindings {g body s r p post}
    (step : RecipientCall g body s r p post) :
    ∀ role, post.heap.memory.carrier role ≠ some s.packet.allocationField ∧
      post.heap.memory.carrier role ≠ some s.packet.domainField := by
  rcases step with ⟨_,entry,rfl⟩
  have corr := entry.pre.correlation entry.ready.live
  have wf := entry.pre.heap.memory
  have fresh := (recipient_payload_supply_fresh entry.fresh).2.1
  have ownA := corr.2.2.2.2.2.2.1
  have ownD := corr.2.2.2.2.2.2.2.1
  have fa : p.payload.allocation ≠ s.packet.allocationField := by
    intro eq; exact fresh.allocationFresh (eq ▸ wf.recorded _ _ ownA)
  have fd : p.payload.domain ≠ s.packet.allocationField := by
    intro eq; exact fresh.domainFresh (eq ▸ wf.recorded _ _ ownA)
  have ga : p.payload.allocation ≠ s.packet.domainField := by
    intro eq; exact fresh.allocationFresh (eq ▸ wf.recorded _ _ ownD)
  have gd : p.payload.domain ≠ s.packet.domainField := by
    intro eq; exact fresh.domainFresh (eq ▸ wf.recorded _ _ ownD)
  intro role
  constructor
  · intro same; cases role with
    | headAllocation => have bad := wf.unique _ _ _ same ownA; cases bad
    | headDomain => have bad := wf.unique _ _ _ same ownA; cases bad
    | tailAllocation => exact fa (Option.some.inj same)
    | tailDomain => exact fd (Option.some.inj same)
  · intro same; cases role with
    | headAllocation => have bad := wf.unique _ _ _ same ownD; cases bad
    | headDomain => have bad := wf.unique _ _ _ same ownD; cases bad
    | tailAllocation => exact ga (Option.some.inj same)
    | tailDomain => exact gd (Option.some.inj same)

theorem recipient_preserves_responsibility {g body s r p post}
    (step : RecipientCall g body s r p post) (i : KnownCall.Site) :
    KnownCall.responsibility post.heap.roots post.heap.memory i =
      KnownCall.responsibility s.heap.roots s.heap.memory i := by
  rw [step.2.2]; cases i <;> rfl

theorem aliases_observe_the_same_caller_post {g body s r p post}
    (step : RecipientCall g body s r p post) (other : Sink)
    (world : other.world = s.heap.world) (target : other.root = s.container) :
    currentThrough post other = some .some := by
  rw [step.2.2]
  simp [currentThrough,recipientPost,consumeDisplacedNone,adoptCandidate,rehome,world,target]

theorem rejected_recipient_keeps_caller_state {g body s r p}
    (bad : ¬ (DefinitionChecked body ∧ Applicable g s r p)) :
    checkedRecipient g body s r p = s := by
  classical
  simp [checkedRecipient,bad]

theorem preconsume_refusal_keeps_original_owner (s : State) :
    (refuse s).heap = s.heap ∧ (refuse s).packet = s.packet ∧ (refuse s).holders = s.holders ∧
    (refuse s).tag = s.tag := ⟨rfl,rfl,rfl,rfl⟩

private theorem none_shape {g s} (wf : WellFormed g s) (tag : s.tag = .none) :
    s.occurrence = none ∧ s.payloadFact = none := by
  constructor
  · cases eq : s.occurrence with
    | none => rfl
    | some o =>
      have bad := wf.shape.1.mpr (by simp [eq]); rw [tag] at bad; cases bad
  · cases eq : s.payloadFact with
    | none => rfl
    | some vf =>
      have bad := wf.shape.2.mpr (by simp [eq]); rw [tag] at bad; cases bad

theorem forgetting_current_knowledge_preserves_wellFormed {g s} (wf : WellFormed g s) :
    WellFormed g (invalidateKnowledge s) := by
  have f := wf.toOwnerFrame
  have core : OwnerFrame g (invalidateKnowledge s) :=
    ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
      f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
  exact ⟨core,wf.currentRecorded,wf.occurrenceRecorded,wf.payloadRecorded,trivial,
    wf.shape,wf.custody,wf.displaced,wf.dependencies,wf.refusal⟩

theorem unknown_current_cannot_prove_exact_none (f : ValueFactId) : ¬ SourceNone .unknown f := by
  simp [SourceNone]

theorem may_some_cannot_prove_exact_none (f : ValueFactId) : ¬ SourceNone .maySome f := by
  simp [SourceNone]

theorem opening_local_loan_preserves_wellFormed {g s} (wf : WellFormed g s) (scope : F2.BindingId) :
    WellFormed g (openLoan s scope) := by
  have f := wf.toOwnerFrame
  have core : OwnerFrame g (openLoan s scope) := by
    refine ⟨history_heap f.heap f.envelope.1 f.envelope.2 (Finset.subset_insert _ _),f.envelope,
      f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
      Finset.mem_insert_of_mem f.localRecorded,f.cover,f.released,f.correlation,?_,f.placementSeparate⟩
    intro live; exact Finset.mem_insert_of_mem (f.placementRecorded live)
  refine ⟨core,wf.currentRecorded,wf.occurrenceRecorded,wf.payloadRecorded,wf.knowledge,
    wf.shape,wf.custody,wf.displaced,?_,wf.refusal⟩
  intro dep mem
  have live := wf.dependencies dep mem
  cases dep with
  | memory fact => exact live
  | scope b =>
    rcases Finset.mem_union.mp live with base|loan
    · exact Finset.mem_union_left _ base
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem loan)

theorem closing_local_loan_preserves_wellFormed {g s} (wf : WellFormed g s) {scope}
    (guard : ScopeGuard s scope) : WellFormed g (closeLoan s scope) := by
  have f := wf.toOwnerFrame
  have core : OwnerFrame g (closeLoan s scope) :=
    ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
      f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
  refine ⟨core,wf.currentRecorded,wf.occurrenceRecorded,wf.payloadRecorded,wf.knowledge,
    wf.shape,wf.custody,wf.displaced,?_,wf.refusal⟩
  intro dep mem
  have live := wf.dependencies dep mem
  cases dep with
  | memory fact => exact live
  | scope b =>
    have different : b ≠ scope := by intro eq; subst b; exact guard.1 mem
    rcases Finset.mem_union.mp live with base|loan
    · exact Finset.mem_union_left _ base
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨different,loan⟩)

theorem refusal_preserves_wellFormed {g s} (wf : WellFormed g s) (none : s.tag = .none) :
    WellFormed g (refuse s) := by
  have f := wf.toOwnerFrame
  have core : OwnerFrame g (refuse s) :=
    ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
      f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
  exact ⟨core,wf.currentRecorded,wf.occurrenceRecorded,wf.payloadRecorded,wf.knowledge,
    wf.shape,wf.custody,wf.displaced,wf.dependencies,fun _ => none⟩

/-- Both runtime variants are handled. Some moves the original packet; None
has no payload to move. No post-WellFormed is an input. -/
theorem extraction_preserves_wellFormed {g s r p} (entry : ExtractApplicable g s r p) :
    WellFormed g (extractPost s p) := by
  have available : s.available = true := entry.sink.2.2.2.1
  cases tag : s.tag with
  | some =>
    have source : Holder.custody ∈ s.holders := entry.pre.custody.mpr ⟨available,tag⟩
    have ready := entry.ready tag
    have moved := rehome_frame (target := .displaced) entry.pre.toOwnerFrame ready source entry.fresh
    have only : (extractPost s p).holders = {.displaced} := by
      simp [extractPost,tag,rehome,singleton_holder entry.pre.toOwnerFrame ready source]
    have core : OwnerFrame g (extractPost s p) := by
      simp only [extractPost,tag,↓reduceIte]
      exact ⟨moved.heap,moved.envelope,moved.context,moved.approved,moved.roots,moved.world,moved.original,
        moved.localDistinct,moved.localRecorded,(fun _ => ⟨.displaced,by simpa only [extractPost,tag,↓reduceIte] using only⟩),moved.released,
        moved.correlation,moved.placementRecorded,moved.placementSeparate⟩
    simp only [extractPost,tag,↓reduceIte,rehome] at core ⊢
    refine ⟨core,Finset.mem_insert_self _ _,?_,?_,⟨available,rfl,rfl⟩,
      ⟨by simp [],by simp []⟩,?_,?_,?_,fun _ => rfl⟩
    · intro o eq; cases eq
    · intro vf eq; cases eq
    · simpa only [extractPost,tag,↓reduceIte,rehome] using (show Holder.custody ∈ (extractPost s p).holders ↔ s.available = true ∧ Tag.none = .some from by rw [only]; simp)
    · simpa only [extractPost,tag,↓reduceIte,rehome] using (show Holder.displaced ∈ (extractPost s p).holders ↔ ∃ old, some (OldSum.mk s.tag .extraction s.knowledge s.currentFact) = some old ∧ old.tag = .some from by rw [only]; simp [tag])
    · simpa only [extractPost,tag,↓reduceIte,rehome] using changed_extra (s := s) (post := extractPost s p) (fun f live => by
          cases f with
          | fixed fact => cases fact <;> simpa [extractPost,tag,rehome,LiveTail.FactLive,KnownCall.FactLive,KnownCall.transfer,KnownCall.State.cell] using live
          | occurrence o => simpa [extractPost,tag,rehome,LiveTail.FactLive,KnownCall.transfer] using live
          | payloadValue o vf => simpa [extractPost,tag,rehome,LiveTail.FactLive,KnownCall.transfer] using live)
        (by intro b mem; simpa only [extractPost,tag,↓reduceIte,rehome] using mem) (by simp [extractPost,tag,rehome]) entry.pre.dependencies entry.change
  | none =>
    have sameHeap : (extractPost s p).heap = s.heap := by simp [extractPost,tag]
    have sameHolders : (extractPost s p).holders = s.holders := by simp [extractPost,tag]
    have f := entry.pre.toOwnerFrame
    have core : OwnerFrame g (extractPost s p) := by
      simp only [extractPost,tag]
      exact ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
        f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
    simp only [extractPost,tag,rehome] at core ⊢
    refine ⟨core,Finset.mem_insert_self _ _,?_,?_,⟨available,rfl,rfl⟩,
      ⟨by simp [],by simp []⟩,?_,?_,?_,fun _ => rfl⟩
    · intro o eq; cases eq
    · intro vf eq; cases eq
    · have absent : Holder.custody ∉ s.holders := by
        intro member; have old := entry.pre.custody.mp member; rw [tag] at old; cases old.2
      simp [absent]
    · have absent : Holder.displaced ∉ s.holders := by
        intro member
        rcases entry.pre.displaced.mp member with ⟨old,present,_⟩
        rw [entry.oldAbsent] at present; cases present
      simp [absent]
    · simpa only [extractPost,tag,↓reduceIte,rehome] using changed_extra (s := s) (post := extractPost s p) (fun _ live => by simpa only [sameHeap] using live)
        (by intro b mem; simpa [extractPost,tag] using mem) (by simp [extractPost,tag]) entry.pre.dependencies entry.change

private theorem rehome_extra {s donor target p} (wf : DependenciesValid s) :
    DependenciesValid (rehome s donor target p) := by
  intro dep mem
  have live := wf dep mem
  cases dep with
  | scope b => exact live
  | memory f =>
    cases f with
    | fixed fact => cases fact <;> simpa [DependencyLive,FactLive,LocalFactLive,LiveTail.FactLive,
        KnownCall.FactLive,KnownCall.State.cell,rehome,KnownCall.transfer] using live
    | occurrence o => exact live
    | payloadValue o vf => exact live

/-- Whole extraction ends C's occurrence but preserves original heap identity. -/
theorem extraction_does_not_transfer_occurrence (s : State) (p : ExtractPlan) :
    (extractPost s p).occurrence = none ∧ (extractPost s p).payloadFact = none ∧
    (extractPost s p).usedOccurrences = s.usedOccurrences ∧
    (extractPost s p).heap.roots = s.heap.roots ∧
    (extractPost s p).packet.ptr = s.packet.ptr ∧
    (extractPost s p).packet.region = s.packet.region ∧
    (extractPost s p).packet.domain = s.packet.domain ∧
    (extractPost s p).packet.dependencies = s.packet.dependencies := by
  cases tag : s.tag <;> simp [extractPost,tag,rehome]

/-- By-value exhaustive match keeps the sole complete owner, or consumes zero
owners in the None branch. Static Option discardability is never changed. -/
theorem recovery_preserves_wellFormed {g s p} (entry : RecoverApplicable g s p) :
    WellFormed g (recoverPost s p) := by
  by_cases present : Holder.displaced ∈ s.holders
  · have ready := entry.ready (entry.pre.displaced.mp present)
    have moved := rehome_frame (target := .saved) entry.pre.toOwnerFrame ready present entry.fresh
    have only : (rehome s .displaced .saved p).holders = {.saved} := by
      simp [rehome,singleton_holder entry.pre.toOwnerFrame ready present]
    have core : OwnerFrame g (recoverPost s p) := by
      simp only [recoverPost,present,↓reduceIte]
      exact ⟨moved.heap,moved.envelope,moved.context,moved.approved,moved.roots,moved.world,moved.original,
        moved.localDistinct,moved.localRecorded,moved.cover,moved.released,moved.correlation,
        moved.placementRecorded,moved.placementSeparate⟩
    simp only [recoverPost,present,↓reduceIte] at core ⊢
    refine ⟨core,entry.pre.currentRecorded,entry.pre.occurrenceRecorded,entry.pre.payloadRecorded,
      entry.pre.knowledge,entry.pre.shape,?_,?_,(rehome_extra (s := s) (donor := .displaced) (target := .saved) (p := p) entry.pre.dependencies),fun _ => entry.empty⟩
    · change Holder.custody ∈ (rehome s .displaced .saved p).holders ↔ s.available = true ∧ s.tag = .some
      rw [only,entry.empty]; simp
    · change Holder.displaced ∈ (rehome s .displaced .saved p).holders ↔ ∃ old : OldSum, (none : Option OldSum) = some old ∧ old.tag = Tag.some
      rw [only]; simp
  · have f := entry.pre.toOwnerFrame
    have core : OwnerFrame g (recoverPost s p) := by
      simp only [recoverPost,present,↓reduceIte]
      exact ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
        f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
    simp only [recoverPost,present,↓reduceIte] at core ⊢
    exact ⟨core,entry.pre.currentRecorded,entry.pre.occurrenceRecorded,entry.pre.payloadRecorded,
      entry.pre.knowledge,entry.pre.shape,entry.pre.custody,by simp [present],
      entry.pre.dependencies,entry.pre.refusal⟩

theorem unpacking_preserves_wellFormed {g s p} (entry : UnpackApplicable g s p) :
    WellFormed g (unpackPost s p) := by
  have present : (if Holder.saved ∈ s.holders then Holder.saved else Holder.packet) ∈ s.holders := by
    split
    · assumption
    · rcases entry.present with h|h; contradiction; exact h
  have moved := rehome_frame (target := .unpacked) entry.pre.toOwnerFrame entry.ready present entry.fresh
  have only : (unpackPost s p).holders = {.unpacked} := by
    by_cases saved : Holder.saved ∈ s.holders
    · simp [unpackPost,rehome,singleton_holder entry.pre.toOwnerFrame entry.ready saved]
    · have packet : Holder.packet ∈ s.holders := by rcases entry.present with h|h; contradiction; exact h
      have only := singleton_holder entry.pre.toOwnerFrame entry.ready packet
      simp only [unpackPost,saved,↓reduceIte,rehome]
      rw [only]
      simp
  have core : OwnerFrame g (unpackPost s p) :=
    ⟨moved.heap,moved.envelope,moved.context,moved.approved,moved.roots,moved.world,moved.original,
      moved.localDistinct,moved.localRecorded,moved.cover,moved.released,moved.correlation,
      moved.placementRecorded,moved.placementSeparate⟩
  refine ⟨core,entry.pre.currentRecorded,entry.pre.occurrenceRecorded,entry.pre.payloadRecorded,
    entry.pre.knowledge,entry.pre.shape,?_,?_,(rehome_extra (s := s) (donor := if Holder.saved ∈ s.holders then .saved else .packet) (target := .unpacked) (p := p) entry.pre.dependencies),fun _ => entry.empty⟩
  · change Holder.custody ∈ (unpackPost s p).holders ↔ s.available = true ∧ s.tag = .some
    rw [only,entry.empty]; simp
  · change Holder.displaced ∈ (unpackPost s p).holders ↔ ∃ old, s.oldSum = some old ∧ old.tag = .some
    rw [only,entry.oldAbsent]; simp

private theorem terminal_extra {g s a d} (entry : TerminalApplicable g s a d) :
    DependenciesValid (terminalPost s a d) := by
  intro dep mem
  have live := entry.pre.dependencies dep mem
  cases dep with
  | scope b => exact live
  | memory f =>
    rcases live with base|container
    · have safe := entry.extra _ mem f rfl
      apply Or.inl
      cases f with
      | fixed fact =>
        cases fact with
        | valueFact place vf =>
          rcases base with ⟨i,typed,hp,hf⟩|link
          · cases i with
            | head => exact Or.inl ⟨.head,typed,hp,hf⟩
            | tail => exact False.elim (safe.1 (by simp [KnownCall.Context.root] at hp hf; subst place; subst vf; rfl))
          · exact Or.inr link
        | domainLive domain =>
          rcases base with ⟨i,alive,identity⟩
          cases i with
          | head => exact ⟨.head,alive,identity⟩
          | tail => exact False.elim (safe.2 (by simp [KnownCall.Context.root] at identity; subst domain; rfl))
      | occurrence o => exact base
      | payloadValue o vf => exact base
    · exact Or.inr container

/-- Later receiver proves its own entry. Release uses the existing typed->slot->
raw->finalize->deallocate chain, not disappearance of the custody place. -/
theorem terminal_preserves_wellFormed {g s a d} (entry : TerminalApplicable g s a d) :
    WellFormed g (terminalPost s a d) := by
  have f := entry.pre.toOwnerFrame
  have heap := LiveTail.subsequent_terminal_preserves_wellFormed entry.base
  have effects := LiveTail.subsequent_terminal_ends_tail_once_preserves_head entry.base
  have core : OwnerFrame g (terminalPost s a d) := by
    refine ⟨heap,⟨rfl,rfl⟩,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,?_,?_,
      (fun _ => rfl),?_,?_,?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem f.localRecorded)
    · intro typed; have released := effects.2.1; change (terminalPost s a d).heap.memory.tail.phase = .released at released; rw [typed] at released; cases released
    · intro typed; have released := effects.2.1; change (terminalPost s a d).heap.memory.tail.phase = .released at released; rw [typed] at released; cases released
    · intro typed; have released := effects.2.1; change (terminalPost s a d).heap.memory.tail.phase = .released at released; rw [typed] at released; cases released
    · intro typed; have released := effects.2.1; change (terminalPost s a d).heap.memory.tail.phase = .released at released; rw [typed] at released; cases released
  refine ⟨core,entry.pre.currentRecorded,entry.pre.occurrenceRecorded,entry.pre.payloadRecorded,
    entry.pre.knowledge,entry.pre.shape,?_,?_,terminal_extra entry,fun _ => entry.empty⟩
  · change Holder.custody ∈ (∅ : Finset Holder) ↔ s.available = true ∧ s.tag = .some
    rw [entry.empty]; simp
  · change Holder.displaced ∈ (∅ : Finset Holder) ↔ ∃ old, s.oldSum = some old ∧ old.tag = .some
    rw [entry.oldAbsent]; simp

theorem terminal_releases_original_tail_once_keeps_head {g s a d} (entry : TerminalApplicable g s a d) :
    (terminalPost s a d).heap.memory.tail.phase = .released ∧
    (terminalPost s a d).heap.memory.tail.releases = 1 ∧
    (terminalPost s a d).heap.memory.head = s.heap.memory.head ∧
    (terminalPost s a d).holders = ∅ ∧
    (terminalPost s a d).heap.roots = s.heap.roots := by
  have effects := LiveTail.subsequent_terminal_ends_tail_once_preserves_head entry.base
  exact ⟨effects.2.1,effects.2.2.1,effects.1,rfl,rfl⟩

theorem terminal_cannot_release_twice {g s a d} (entry : TerminalApplicable g s a d) :
    ∀ a2 raw, ¬ KnownCall.CanDeallocate (terminalPost s a d).heap.roots
      (terminalPost s a d).heap.memory a2 raw :=
  (LiveTail.subsequent_terminal_no_resurrection_or_double_release entry.base).2

theorem final_exact_none_consumption_preserves_wellFormed {g s} (entry : FinalApplicable g s) :
    WellFormed g (consumeFinalNone s) := by
  have f := entry.pre.toOwnerFrame
  have core : OwnerFrame g (consumeFinalNone s) :=
    ⟨f.heap,f.envelope,f.context,f.approved,f.roots,f.world,f.original,f.localDistinct,
      f.localRecorded,f.cover,f.released,f.correlation,f.placementRecorded,f.placementSeparate⟩
  refine ⟨core,entry.pre.currentRecorded,entry.pre.occurrenceRecorded,entry.pre.payloadRecorded,trivial,
    entry.pre.shape,?_,entry.pre.displaced,?_,entry.pre.refusal⟩
  · have absent : Holder.custody ∉ s.holders := by
      intro member; have someTag := (entry.pre.custody.mp member).2
      rw [entry.exactNone.2.1] at someTag; cases someTag
    simp [consumeFinalNone,absent]
  · exact changed_extra (s := s) (post := consumeFinalNone s) (fun _ live => live)
      (by intro b mem; exact mem) rfl entry.pre.dependencies entry.change

theorem noncopy_holder_cannot_duplicate {g s} (wf : WellFormed g s)
    (live : s.heap.memory.tail.phase = .typed) {a b}
    (ha : a ∈ s.holders) (hb : b ∈ s.holders) : a = b := by
  rcases wf.cover live with ⟨h,only⟩
  rw [only] at ha hb
  exact (Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm

theorem live_noncopy_owner_cannot_be_forgotten {g s} (wf : WellFormed g s)
    (live : s.heap.memory.tail.phase = .typed) : s.holders.Nonempty := by
  rcases wf.cover live with ⟨h,only⟩
  rw [only]; exact Finset.singleton_nonempty _

theorem any_surviving_sink_occurrence_blocks_extract {g s r p o}
    (dep : LiveTail.Dependency.memory (.occurrence o) ∈ s.extraDependencies)
    (current : s.occurrence = some o) : ¬ ExtractApplicable g s r p := by
  intro entry
  exact entry.change _ dep _ rfl current

theorem escaped_sink_scope_blocks_recipient {g s r p}
    (escape : LiveTail.Dependency.scope r.scope ∈ s.extraDependencies) : ¬ Applicable g s r p := by
  intro entry; exact entry.sinkScope.1 escape

theorem invalidated_current_knowledge_blocks_recipient {g s r p} :
    ¬ Applicable g (invalidateKnowledge s) r p := by
  intro entry; exact unknown_current_cannot_prove_exact_none _ entry.exactNone

theorem readonly_sink_blocks_recipient {g s r p} (readOnly : r.write = false) :
    ¬ Applicable g s r p := by
  intro entry; have write := entry.sink.2.2.2.2.2.2.1
  rw [readOnly] at write; cases write

theorem wrong_world_blocks_recipient {g s r p} (wrong : r.world ≠ s.heap.world) :
    ¬ Applicable g s r p := by intro entry; exact wrong entry.sink.1

theorem historical_occurrence_cannot_be_reused {g s r p}
    (used : p.occurrence ∈ s.usedOccurrences) : ¬ Applicable g s r p := by
  intro entry; exact entry.fresh.2.2.2.2.2.2 used

theorem elsewhere_one_arm_none_is_forbidden (s : State) : ¬ NoneOnlyLegal .elsewhere s := id

theorem runtime_none_does_not_enable_store_drop_or_bool_failure :
    ¬ DefinitionChecked [.storeSome,.consumeDisplacedNone,.returnUnit] ∧
    ¬ DefinitionChecked [.replaceSome,.dropOld,.returnUnit] ∧
    ¬ DefinitionChecked [.replaceSome,.someWildcard,.returnUnit] ∧
    ¬ DefinitionChecked [.replaceSome,.consumeDisplacedNone,.returnFailure] := by
  simp [DefinitionChecked,selectedBody]

/-- Historical allocation consults BOTH the prior producer history and local
C history. Neither ended head occurrences nor earlier C occurrences are reusable. -/
theorem recipient_fresh_in_combined_occurrence_history {g s r p} (entry : Applicable g s r p) :
    p.occurrence ∉ s.heap.usedOccurrences ∪ s.usedOccurrences ∧
    p.occurrence ∈ (recipientPost s p).usedOccurrences ∧
    s.usedOccurrences ⊆ (recipientPost s p).usedOccurrences := by
  refine ⟨?_,Finset.mem_insert_self _ _,Finset.subset_insert _ _⟩
  intro reused
  rcases Finset.mem_union.mp reused with heap|container
  · exact entry.heapFresh.1 heap
  · exact entry.fresh.2.2.2.2.2.2 container

/-- The independently checked formal parameter owns the SAME heap, with fresh
ordinary binding identities. The callee does not mint a heap allocation/domain. -/
theorem recipient_formal_entry_preserves_original_owner {g s r p} (entry : Applicable g s r p) :
    OwnerFrame g (rehome s .packet .formal p.formal) ∧
    (rehome s .packet .formal p.formal).holders = {.formal} ∧
    (rehome s .packet .formal p.formal).heap.memory.tail = s.heap.memory.tail ∧
    (rehome s .packet .formal p.formal).packet.ptr = s.packet.ptr ∧
    (rehome s .packet .formal p.formal).packet.region = s.packet.region ∧
    (rehome s .packet .formal p.formal).packet.domain = s.packet.domain := by
  refine ⟨rehome_frame entry.pre.toOwnerFrame entry.ready entry.packet (recipient_formal_supply_fresh entry.fresh),
    ?_,rfl,rfl,rfl,rfl⟩
  simp [rehome,singleton_holder entry.pre.toOwnerFrame entry.ready entry.packet]

theorem recipient_formal_bindings_consumed_on_unit_return {g s r p} (entry : Applicable g s r p) :
    (recipientPost s p).heap.memory.carrier .tailAllocation ≠ some p.formal.allocation ∧
    (recipientPost s p).heap.memory.carrier .tailDomain ≠ some p.formal.domain := by
  constructor
  · intro same
    have eq : p.payload.allocation = p.formal.allocation := Option.some.inj same
    have indexEq : (5 : Nat) = 2 := entry.fresh.1.getElem_inj_iff.mp
      (show p.bindings[5]'(by simp [AdoptPlan.bindings]) = p.bindings[2]'(by simp [AdoptPlan.bindings]) from eq)
    cases indexEq
  · intro same
    have eq : p.payload.domain = p.formal.domain := Option.some.inj same
    have indexEq : (6 : Nat) = 3 := entry.fresh.1.getElem_inj_iff.mp
      (show p.bindings[6]'(by simp [AdoptPlan.bindings]) = p.bindings[3]'(by simp [AdoptPlan.bindings]) from eq)
    cases indexEq

theorem ended_loan_never_grants_write_permission {s r}
    (ended : r.scope ∉ s.loans) : ¬ SinkValid s r := by
  intro valid; exact ended valid.2.2.2.2.1


theorem fresh_local_loan_preserves_wellFormed {g s scope post} (step : LoanStep g s scope post) :
    WellFormed g post := by
  rw [step.post]; exact opening_local_loan_preserves_wellFormed step.pre scope

theorem historical_loan_scope_cannot_be_reopened {g s scope post}
    (used : scope ∈ s.heap.memory.usedBindings) : ¬ LoanStep g s scope post := by
  intro step; exact step.fresh used

end
end NewLang.Adjunct.Custody
