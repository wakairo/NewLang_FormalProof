import NewLang.Adjunct.LiveTail
import Mathlib.Data.List.Nodup

namespace NewLang.Adjunct.LiveTail
open F0 F1.Backing F1.Occupancy
noncomputable section

private theorem planned_pair {s p} (fresh : FreshPlan s p) {i j : Nat}
    (hi : i < p.bindings.length) (hj : j < p.bindings.length) (different : i ≠ j) :
    KnownCall.FreshParameters s.memory p.bindings[i] p.bindings[j] := by
  refine ⟨fresh.unused _ (List.getElem_mem hi),fresh.unused _ (List.getElem_mem hj),?_,
    (fresh.valueScopes _ (List.getElem_mem hi)).1,(fresh.valueScopes _ (List.getElem_mem hj)).2⟩
  exact fun same => different (fresh.distinct.getElem_inj_iff.mp same)

theorem fresh_formal_parameters {s p} (fresh : FreshPlan s p) :
    KnownCall.FreshParameters s.memory p.formalA p.formalD :=
  planned_pair fresh (i := 0) (j := 1) (by simp [Plan.bindings]) (by simp [Plan.bindings]) (by decide)

theorem fresh_return_fields {s p} (fresh : FreshPlan s p) :
    KnownCall.FreshParameters s.memory p.returnA p.returnD :=
  planned_pair fresh (i := 6) (j := 7) (by simp [Plan.bindings]) (by simp [Plan.bindings]) (by decide)

private theorem history_extension {c : KnownCall.Context} {s : KnownCall.State} {u : Finset F2.BindingId}
    (wf : KnownCall.WellFormed c s) (more : s.usedBindings ⊆ u) :
    KnownCall.WellFormed c {s with usedBindings := u} :=
  ⟨wf.allocation,wf.domain,wf.typedDomain,wf.slotDomain,wf.releasedDomain,wf.releaseCount,
    fun r b h => more (wf.recorded r b h),wf.unique,wf.dependencies⟩

private theorem producer_memory_shadow (s : State) (p : Plan) :
    (producerPost s p).memory =
      {KnownCall.transfer s.memory p.returnA p.returnD with
        usedBindings := (producerPost s p).memory.usedBindings} := by
  cases s
  dsimp [producerPost,package,detach,formalEntry,KnownCall.transfer]
  congr 1
  funext r; cases r <;> rfl

private theorem fresh_head_context {s p} (wf : WellFormed s) (fresh : FreshPlan s p)
    {g} (valid : KnownCall.ContextValid g s.roots) :
    KnownCall.ContextValid g (producerPost s p).roots := by
  refine ⟨valid.regions,valid.locations,valid.places,valid.incarnations,?_,valid.domains,valid.packages,
    valid.nonempty,(by intro i; cases i with | head => exact valid.full .head | tail => exact valid.full .tail),
    (by intro i; cases i with | head => exact valid.exactSize .head | tail => exact valid.exactSize .tail),valid.disjoint⟩
  intro same
  change p.parentFact = s.roots.tail.currentFact at same
  exact fresh.parentFresh (same.symm ▸ wf.tailRecorded)

private theorem parent_change_preserves_known_wf {c : KnownCall.Context} {s : KnownCall.State}
    {parent : ValueFactId} (wf : KnownCall.WellFormed c s)
    (guard : ∀ f, f ∈ c.head.dependencies ∨ f ∈ c.tail.dependencies ∨ f ∈ s.externalDependencies →
      f ≠ .valueFact c.head.place c.head.currentFact) :
    KnownCall.WellFormed {c with head := {c.head with currentFact := parent}} s := by
  have retained : ∀ f, (f ∈ c.head.dependencies ∨ f ∈ c.tail.dependencies ∨ f ∈ s.externalDependencies) →
      KnownCall.FactLive c s f → KnownCall.FactLive {c with head := {c.head with currentFact := parent}} s f := by
    intro f member live
    cases f with
    | valueFact place vf =>
      rcases live with ⟨i,typed,hp,hf⟩
      cases i with
      | head =>
        have eq : F0.Fact.valueFact place vf = .valueFact c.head.place c.head.currentFact := by
          simp [KnownCall.Context.root] at hp hf; subst place; subst vf; rfl
        exact False.elim (guard _ member eq)
      | tail => exact ⟨.tail,typed,hp,hf⟩
    | domainLive d =>
      rcases live with ⟨i,alive,identity⟩
      refine ⟨i,alive,?_⟩; cases i <;> exact identity
  refine ⟨wf.allocation,wf.domain,wf.typedDomain,wf.slotDomain,wf.releasedDomain,wf.releaseCount,
    wf.recorded,wf.unique,?_,?_⟩
  · intro i typed f member
    cases i with
    | head => exact retained f (Or.inl member) (wf.dependencies.1 .head typed f member)
    | tail => exact retained f (Or.inr (Or.inl member)) (wf.dependencies.1 .tail typed f member)
  · intro f member; exact retained f (Or.inr (Or.inr member)) (wf.dependencies.2 f member)

private theorem producer_known_wf {g s r args p} (entry : ActualCallApplicable g s r args p) :
    KnownCall.WellFormed (producerPost s p).roots (producerPost s p).memory := by
  have moved := KnownCall.transfer_preserves_wellFormed entry.pre.memory entry.tail (fresh_return_fields entry.fresh)
  have extended : KnownCall.WellFormed s.roots (producerPost s p).memory := by
    rw [producer_memory_shadow]
    apply history_extension moved
    intro b member
    simp [producerPost,package,detach,formalEntry,KnownCall.transfer] at member ⊢
    tauto
  exact parent_change_preserves_known_wf extended entry.detach.1

private theorem producer_dependency_facts_retained {s p}
    (guard : DetachGuard s) {f : F1.Conditional.Fact}
    (member : Dependency.memory f ∈ survivingDependencies s) (live : FactLive s f) :
    FactLive (producerPost s p) f := by
  have safe := guard.2 _ member f rfl
  cases f with
  | fixed f =>
    cases f with
    | valueFact place vf =>
      rcases live with ⟨i,typed,hp,hf⟩|⟨typed,hp,hf⟩
      · cases i with
        | head =>
          exact False.elim (safe (Or.inl (by simpa [KnownCall.Context.root] using ⟨hp.symm,hf.symm⟩)))
        | tail => exact Or.inl ⟨.tail,typed,hp,hf⟩
      · exact False.elim (safe (Or.inr ⟨hp,hf⟩))
    | domainLive d =>
      rcases live with ⟨i,alive,identity⟩
      refine ⟨i,alive,?_⟩; cases i <;> exact identity
  | occurrence o => exact False.elim (safe live.2)
  | payloadValue o vf => exact False.elim (safe live.2)

private theorem producer_dependencies {s p} (wf : WellFormed s) (guard : DetachGuard s) :
    DependenciesValid (producerPost s p) := by
  intro d member
  have pre : d ∈ survivingDependencies s := member
  have live := wf.dependencies d pre
  cases d with
  | scope b => exact live
  | memory f => exact producer_dependency_facts_retained guard pre live

private theorem producer_package_shape {g s r args p} (entry : ActualCallApplicable g s r args p) :
    PackageShape (producerPost s p) := by
  refine ⟨makeBundle s p.returnPlacement p.returnA p.returnD,rfl,?_,?_,?_⟩
  · refine ⟨rfl,rfl,rfl,rfl,entry.tail.live,entry.pre.memory.typedDomain .tail entry.tail.live,rfl,rfl,rfl⟩
  · simp [producerPost,package,KnownCall.transfer,makeBundle]
  · intro role present
    cases role with
    | headAllocation =>
      exact entry.fresh.unused _ (by simp [Plan.bindings,makeBundle]) (entry.pre.memory.recorded _ _ present)
    | headDomain =>
      exact entry.fresh.unused _ (by simp [Plan.bindings,makeBundle]) (entry.pre.memory.recorded _ _ present)
    | tailAllocation =>
      have eq : p.returnA = p.returnPlacement := Option.some.inj present
      have impossible := entry.fresh.distinct.getElem_inj_iff (i := 5) (j := 6) (hi := by simp [Plan.bindings])
        (hj := by simp [Plan.bindings])
      have bad : (5 : Nat) = 6 := impossible.mp eq.symm
      omega
    | tailDomain =>
      have eq : p.returnD = p.returnPlacement := Option.some.inj present
      have impossible := entry.fresh.distinct.getElem_inj_iff (i := 5) (j := 7) (hi := by simp [Plan.bindings])
        (hj := by simp [Plan.bindings])
      have bad : (5 : Nat) = 7 := impossible.mp eq.symm
      omega

/-- The still-live producer derives its post invariant from entry and finite
survivor conditions. The previous terminal receiver theorem is not used here. -/
theorem producer_preserves_wellFormed {g body s r args p post}
    (step : ProducerCall g body s r args p post) : WellFormed post := by
  rcases step with ⟨_,entry,rfl⟩
  refine ⟨producer_known_wf entry,entry.pre.layout,⟨rfl,rfl⟩,?_,?_,?_,?_,?_,
    producer_dependencies entry.pre entry.detach,producer_package_shape entry,?_⟩
  · simp [producerPost,package,detach]
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem entry.pre.tailRecorded)
  · simp [producerPost,package,detach]
  · intro vf present; cases present
  · intro o present; cases present
  · intro b live
    have recorded := entry.pre.scopeRecorded b live
    simp [producerPost,package,detach,formalEntry,KnownCall.transfer]
    simp_all

theorem producer_original_tail_and_head_live {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    post.roots.tail = s.roots.tail ∧ post.memory.tail = s.memory.tail ∧
    post.memory.head = s.memory.head ∧ post.memory.tail.phase = .typed ∧
    post.memory.head.phase = .typed ∧ post.memory.tail.releases = 0 := by
  rcases step with ⟨_,entry,rfl⟩
  have zero : s.memory.tail.releases = 0 := by
    simpa [KnownCall.State.cell,entry.tail.live] using entry.pre.memory.releaseCount .tail
  exact ⟨rfl,rfl,rfl,entry.tail.live,entry.tail.headLive,zero⟩

theorem producer_changes_head_link_and_parent_fact {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    post.link.payload = none ∧ post.link.occurrence = none ∧ post.link.payloadFact = none ∧
    post.link.currentFact = p.linkFact ∧ post.roots.head.currentFact = p.parentFact ∧
    post.layout = s.layout ∧ post.roots.head.incarnation = s.roots.head.incarnation ∧
    post.roots.head.extent = s.roots.head.extent ∧ post.roots.head.domain = s.roots.head.domain := by
  rw [step.2.2]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem producer_returns_complete_original_owner {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    ∃ b, post.bundle = some b ∧ CarriesLiveH post b ∧ b.copyable = false ∧ b.discardable = false := by
  rcases step with ⟨body,entry,rfl⟩
  rcases producer_package_shape entry with ⟨b,present,correlation,_,_⟩
  exact ⟨b,present,correlation,rfl,rfl⟩

theorem producer_no_direct_donor_or_formal_owner {g body s r args p post}
    (step : ProducerCall g body s r args p post) (a d : F2.BindingId) :
    ¬ DirectTailAvailable post a d := by
  rw [step.2.2]; simp [DirectTailAvailable,producerPost,package]

theorem producer_result_does_not_escape_head_scope {g body s r args p post}
    (step : ProducerCall g body s r args p post) {b : Bundle} (present : post.bundle = some b) :
    ∀ scope ∈ s.scopes, Dependency.scope scope ∉ b.dependencies := by
  rcases step with ⟨_,entry,rfl⟩
  have eq : b = makeBundle s p.returnPlacement p.returnA p.returnD := Option.some.inj present.symm
  subst b; exact entry.nonescape

theorem rejected_call_preserves_public_state {g body s r args p}
    (bad : ¬ (DefinitionChecked body ∧ ActualCallApplicable g s r args p)) :
    checkedProducer g body s r args p = (s,none) := by
  classical
  simp [checkedProducer,bad]

/-- Independent definition certificate is conditional for arbitrary uncorrelated
records; it neither selects a caller nor proves its entry relation. -/
def ConditionalDefinition (g : Geometry) (body : List Command) : Prop :=
  DefinitionChecked body ∧ ∀ s r args p, ActualCallApplicable g s r args p →
    WellFormed (producerPost s p) ∧
    ∃ b, (producerPost s p).bundle = some b ∧ CarriesLiveH (producerPost s p) b

theorem selected_producer_definition_is_conditional (g : Geometry) : ConditionalDefinition g selectedBody := by
  refine ⟨rfl,?_⟩
  intro s r args p entry
  have step : ProducerCall g selectedBody s r args p (producerPost s p) := ⟨rfl,entry,rfl⟩
  refine ⟨producer_preserves_wellFormed step,?_⟩
  rcases producer_returns_complete_original_owner step with ⟨b,present,correlated,_,_⟩
  exact ⟨b,present,correlated⟩


theorem producer_preserves_context {g body s r args p post}
    (step : ProducerCall g body s r args p post) : KnownCall.ContextValid g post.roots := by
  rcases step with ⟨_,entry,rfl⟩
  exact fresh_head_context entry.pre entry.fresh entry.context

theorem producer_preserves_original_responsibilities {g body s r args p post}
    (step : ProducerCall g body s r args p post) (i : KnownCall.Site) :
    KnownCall.responsibility post.roots post.memory i = KnownCall.responsibility s.roots s.memory i := by
  rw [step.2.2]; cases i <;> rfl

theorem producer_donor_carriers_consumed {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    ∀ role, post.memory.carrier role ≠ some args.tail.allocationBinding ∧
      post.memory.carrier role ≠ some args.tail.domainBinding := by
  rcases step with ⟨_,entry,rfl⟩
  have moved := KnownCall.transfer_consumes_donor entry.pre.memory entry.tail (fresh_return_fields entry.fresh)
  intro role; rw [producer_memory_shadow]
  exact ⟨moved.2.2.1 role,moved.2.2.2 role⟩

theorem producer_packet_uses_actual_original_values {g body s r args p post}
    (step : ProducerCall g body s r args p post) {b : Bundle} (present : post.bundle = some b) :
    b.world = args.world ∧ b.ptr = args.tail.ptr.token ∧
    b.region = args.tail.allocationRegion ∧ b.domain = args.tail.domain := by
  rcases step with ⟨_,entry,rfl⟩
  have eq : b = makeBundle s p.returnPlacement p.returnA p.returnD := Option.some.inj present.symm
  subst b
  exact ⟨entry.world.symm,entry.tail.ptrRoot.symm,entry.tail.allocationRegion.symm,entry.tail.domainIdentity.symm⟩

theorem producer_old_link_occurrence_ended {g body s r args p post}
    (step : ProducerCall g body s r args p post) (o : F1.Conditional.OccurrenceId) :
    ¬ FactLive post (.occurrence o) := by
  rw [step.2.2]; simp [FactLive,producerPost,package,detach]

theorem producer_parent_and_link_facts_fresh {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    p.parentFact ∉ s.usedFacts ∧ p.linkFact ∉ s.usedFacts ∧ p.parentFact ≠ p.linkFact ∧
    p.parentFact ∈ post.usedFacts ∧ p.linkFact ∈ post.usedFacts ∧ s.usedFacts ⊆ post.usedFacts ∧
    post.usedOccurrences = s.usedOccurrences := by
  rcases step with ⟨_,entry,rfl⟩
  refine ⟨entry.fresh.parentFresh,entry.fresh.linkFresh,entry.fresh.differentFacts,?_,?_,?_,rfl⟩
  · simp [producerPost,package,detach]
  · simp [producerPost,package,detach]
  · intro f member; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)

theorem producer_tail_still_current {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    KnownCall.CurrentLocator post.roots post.memory args.tail.ptr.token ∧
    KnownCall.Governs post.roots post.memory s.roots.tail.incarnation s.roots.tail.domain := by
  rcases step with ⟨_,entry,rfl⟩
  exact ⟨⟨.tail,entry.tail.live,entry.tail.ptrRoot⟩,⟨.tail,entry.tail.live,rfl,rfl⟩⟩

/-- Future receiver applicability still needs its own survivor guards. This
lemma only reconstructs the original tail entry predicates, not a legal call. -/
theorem producer_retains_tail_requirements {g body s r args p post}
    (step : ProducerCall g body s r args p post) :
    KnownCall.RequiredAtEntry post.roots post.memory
      {args.tail with allocationBinding := p.returnA, domainBinding := p.returnD} := by
  rcases step with ⟨_,entry,rfl⟩
  exact ⟨entry.tail.headLive,entry.tail.live,entry.tail.ptrRoot,entry.tail.ptrRegion,entry.tail.read,
    entry.tail.issued,entry.tail.access,entry.tail.allocationRegion,rfl,entry.tail.domainIdentity,rfl,
    (entry.fresh.valueScopes _ (by simp [Plan.bindings])).1,
    (entry.fresh.valueScopes _ (by simp [Plan.bindings])).2,
    entry.tail.rootScope,entry.tail.domainScope,entry.tail.regionScope,entry.tail.discardable,entry.tail.platform⟩

theorem scope_exit_preserves_wellFormed {s} (wf : WellFormed s) (guard : ScopeExitGuard s) :
    WellFormed (closeHeadScope s) := by
  refine ⟨wf.memory,wf.layout,wf.shape,wf.parentRecorded,wf.tailRecorded,wf.linkRecorded,
    wf.payloadRecorded,wf.occurrenceRecorded,?_,wf.package,
    (fun b live => wf.scopeRecorded b (Finset.mem_of_mem_erase live))⟩
  intro d member
  have live := wf.dependencies d member
  cases d with
  | memory f => exact live
  | scope b =>
    have different : b ≠ s.headScope := by intro eq; subst b; exact guard member
    exact Finset.mem_erase.mpr ⟨different,live⟩

theorem known_return_after_scope_is_wellFormed {s} (origin : KnownReturnAfterScope s) : WellFormed s := by
  rcases origin with ⟨before,⟨g,body,pre,r,args,p,step⟩,guard,rfl⟩
  exact scope_exit_preserves_wellFormed (producer_preserves_wellFormed step) guard

private theorem after_scope_entry {s b a d} (input : UnpackInput s b a d) :
    ∃ args, KnownCall.RequiredAtEntry s.roots s.memory args := by
  rcases input.origin with ⟨before,⟨g,body,pre,r,args,p,step⟩,guard,rfl⟩
  have entry := producer_retains_tail_requirements step
  exact ⟨_,by simpa only [closeHeadScope] using entry⟩

theorem whole_destructure_preserves_wellFormed {s b a d} (input : UnpackInput s b a d) :
    WellFormed (unpack s a d) := by
  have wf := known_return_after_scope_is_wellFormed input.origin
  rcases after_scope_entry input with ⟨args,entry⟩
  exact ⟨KnownCall.transfer_preserves_wellFormed wf.memory entry input.fresh,wf.layout,wf.shape,
    wf.parentRecorded,wf.tailRecorded,wf.linkRecorded,wf.payloadRecorded,wf.occurrenceRecorded,wf.dependencies,rfl,
    (fun b live => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.scopeRecorded b live)))⟩

theorem whole_destructure_consumes_package {s b a d} (_input : UnpackInput s b a d) :
    (unpack s a d).bundle = none ∧ (unpack s a d).stage = .unpacked ∧
    DirectTailAvailable (unpack s a d) a d ∧
    (unpack s a d).roots.tail = s.roots.tail ∧ (unpack s a d).memory.tail = s.memory.tail := by
  exact ⟨rfl,rfl,⟨Or.inr (Or.inr rfl),rfl,rfl⟩,rfl,rfl⟩

theorem whole_destructure_cannot_repeat {s b a d} (_input : UnpackInput s b a d)
    (b2 : Bundle) (a2 d2 : F2.BindingId) : ¬ UnpackInput (unpack s a d) b2 a2 d2 := by
  intro again; have present := again.present; change none = some b2 at present; cases present

theorem whole_destructure_preserves_tail_correlation {s b a d} (input : UnpackInput s b a d) :
    b.world = (unpack s a d).world ∧
    KnownCall.CurrentLocator (unpack s a d).roots (unpack s a d).memory b.ptr ∧
    b.region = (unpack s a d).roots.tail.extent.region ∧ b.domain = (unpack s a d).roots.tail.domain := by
  have wf := known_return_after_scope_is_wellFormed input.origin
  have shape := wf.package
  simp only [PackageShape,input.returned] at shape
  rcases shape with ⟨value,present,correlation,_,_⟩
  have same : b = value := Option.some.inj (input.present.symm.trans present)
  subst value
  exact ⟨correlation.1,⟨.tail,correlation.2.2.2.2.1,correlation.2.1⟩,correlation.2.2.1,correlation.2.2.2.1⟩

private theorem terminal_precise_dependencies {g s args a d} (call : TerminalCall g s args a d) :
    DependenciesValid (terminalPost s a d) := by
  rcases call with ⟨wf,stage,scope,world,base,guard⟩
  have targetLive := base.2.2.1.live
  intro dep member
  have survivor : dep ∈ s.externalDependencies ∪ s.ptrDependencies := by
    simpa [survivingDependencies,terminalPost,KnownCall.callPost,KnownCall.receiver,KnownCall.deallocate] using member
  have pre : dep ∈ survivingDependencies s := by
    simp [survivingDependencies,targetLive] at survivor ⊢
    tauto
  have live := wf.dependencies dep pre
  cases dep with
  | scope b => exact live
  | memory f =>
    have safe := guard _ survivor f rfl
    cases f with
    | fixed f =>
      cases f with
      | valueFact place vf =>
        rcases live with ⟨i,typed,hp,hf⟩|⟨typed,hp,hf⟩
        · cases i with
          | head => exact Or.inl ⟨.head,typed,hp,hf⟩
          | tail =>
            exact False.elim (safe.1 (by simp [KnownCall.Context.root] at hp hf; subst place; subst vf; rfl))
        · exact Or.inr ⟨typed,hp,hf⟩
      | domainLive domain =>
        rcases live with ⟨i,alive,identity⟩
        cases i with
        | head => exact ⟨.head,alive,identity⟩
        | tail => exact False.elim (safe.2 (by simp [KnownCall.Context.root] at identity; subst domain; rfl))
    | occurrence o => exact live
    | payloadValue o vf => exact live

theorem subsequent_terminal_preserves_wellFormed {g s args a d}
    (call : TerminalCall g s args a d) : WellFormed (terminalPost s a d) := by
  rcases call with ⟨wf,stage,scope,world,base,guard⟩
  refine ⟨KnownCall.known_call_preserves_wellFormed base,wf.layout,wf.shape,wf.parentRecorded,
    wf.tailRecorded,wf.linkRecorded,wf.payloadRecorded,wf.occurrenceRecorded,?_,rfl,
    (fun b live => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.scopeRecorded b live)))⟩
  exact terminal_precise_dependencies ⟨wf,stage,scope,world,base,guard⟩

theorem subsequent_terminal_ends_tail_once_preserves_head {g s args a d}
    (call : TerminalCall g s args a d) :
    (terminalPost s a d).memory.head = s.memory.head ∧
    (terminalPost s a d).memory.tail.phase = .released ∧
    (terminalPost s a d).memory.tail.releases = 1 ∧
    (terminalPost s a d).memory.carrier .headAllocation = s.memory.carrier .headAllocation ∧
    (terminalPost s a d).memory.carrier .headDomain = s.memory.carrier .headDomain := by
  rcases call with ⟨wf,stage,scope,world,base,guard⟩
  have effects := KnownCall.call_ends_only_original_tail base
  have frame := KnownCall.known_call_preserves_head_authorities base
  exact ⟨effects.1,effects.2.2.1,effects.2.2.2.2.1,frame.1,frame.2⟩

theorem subsequent_terminal_no_resurrection_or_double_release {g s args a d}
    (call : TerminalCall g s args a d) :
    ¬ KnownCall.CurrentLocator s.roots (terminalPost s a d).memory
      ⟨s.roots.tail.location,s.roots.tail.incarnation⟩ ∧
    ∀ a2 raw, ¬ KnownCall.CanDeallocate s.roots (terminalPost s a d).memory a2 raw := by
  rcases call with ⟨wf,stage,scope,world,base,guard⟩
  refine ⟨?_,KnownCall.known_call_cannot_double_release base⟩
  change ¬ KnownCall.CurrentLocator s.roots (KnownCall.receiver (KnownCall.transfer s.memory a d)) _
  exact KnownCall.ended_tail_ptr_cannot_reacquire base.1


theorem actual_call_keeps_head_tail_domains_distinct {g s r args p}
    (entry : ActualCallApplicable g s r args p) : r.domain ≠ args.tail.domain := by
  intro same
  apply entry.context.domains
  rw [← entry.head.governing,← entry.tail.domainIdentity]
  exact same

theorem wrong_world_rejects_call {g s r args p} (wrong : args.world ≠ s.world) :
    ¬ ActualCallApplicable g s r args p := fun h => wrong h.world

theorem wrong_region_rejects_call {g s r args p} (wrong : args.tail.allocationRegion ≠ s.roots.tail.extent.region) :
    ¬ ActualCallApplicable g s r args p := fun h => wrong h.tail.allocationRegion

theorem wrong_domain_rejects_call {g s r args p} (wrong : args.tail.domain ≠ s.roots.tail.domain) :
    ¬ ActualCallApplicable g s r args p := fun h => wrong h.tail.domainIdentity

theorem wrong_current_link_rejects_call {g s r args p} (wrong : s.link.payload ≠ some (args.world,args.tail.ptr.token)) :
    ¬ ActualCallApplicable g s r args p := fun h => wrong h.head.someExactTail

theorem readonly_head_ref_rejects_call {g s r args p} (readonly : r.write = false) :
    ¬ ActualCallApplicable g s r args p := by
  intro h; have write := h.head.write; rw [readonly] at write; cases write

theorem expired_head_scope_rejects_call {g s r args p} (expired : r.scope ∉ s.scopes) :
    ¬ ActualCallApplicable g s r args p := fun h => expired h.head.liveScope

theorem escaping_owner_dependency_rejects_call {g s r args p} {scope : F2.BindingId}
    (live : scope ∈ s.scopes) (dependent : Dependency.scope scope ∈ ownerDependencies s) :
    ¬ ActualCallApplicable g s r args p := fun h => h.nonescape scope live dependent

theorem ended_link_dependency_rejects_call {g s r args p} {f : F1.Conditional.Fact}
    (dependent : Dependency.memory f ∈ survivingDependencies s) (ended : EndsAtDetach s f) :
    ¬ ActualCallApplicable g s r args p := fun h => h.detach.2 _ dependent f rfl ended

theorem mismatched_bundle_region_has_no_certificate {s b} (wrong : b.region ≠ s.roots.tail.extent.region) :
    ¬ CarriesLiveH s b := fun h => wrong h.2.2.1

theorem missing_bundle_domain_carrier_has_no_certificate {s b}
    (missing : s.memory.carrier .tailDomain = none) : ¬ CarriesLiveH s b := by
  intro h; have present := h.2.2.2.2.2.2.2.1; rw [missing] at present; cases present

theorem ended_root_has_no_live_return_certificate {s b} (ended : s.memory.tail.phase = .released) :
    ¬ CarriesLiveH s b := by
  intro h; have live := h.2.2.2.2.1; rw [ended] at live; cases live

theorem terminal_receiver_is_not_live_return (s : State) (b : Bundle) :
    ¬ CarriesLiveH {s with memory := KnownCall.receiver s.memory} b :=
  ended_root_has_no_live_return_certificate rfl


end
end NewLang.Adjunct.LiveTail
