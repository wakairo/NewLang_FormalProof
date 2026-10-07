import NewLang.F3.Memory.SumLifetime

namespace NewLang.F3.Memory.SumLifetime
open F0 F1 F1.Backing F1.Occupancy
noncomputable section

theorem coarse_live {s : Conditional.State} {l r} :
    (coarse s).occupancy l = .live r ↔ l ∈ s.liveRoots ∧ coarseRoot (s.root l) = r := by
  by_cases h : l ∈ s.liveRoots <;> simp [coarse,coarseRoot,h]

theorem coarse_survives {s : Conditional.State} {p} :
    F0.Survives (coarse s) p ↔ Conditional.Survives s p := by
  simp only [F0.Survives,IsInstalled,Carries,coarse_live,Conditional.Survives]
  constructor
  · rintro (⟨l,r,⟨live,rfl⟩,pkg⟩|loose)
    · exact Or.inr ⟨l,live,pkg⟩
    · exact Or.inl loose
  · rintro (loose|⟨l,live,pkg⟩)
    · exact Or.inr loose
    · exact Or.inl ⟨l,coarseRoot (s.root l),⟨live,rfl⟩,pkg⟩

theorem coarse_live_facts {s : Conditional.State} {f : F0.Fact} :
    f ∈ F0.LiveFacts (coarse s) ↔ Conditional.Fact.fixed f ∈ Conditional.LiveFacts s := by
  cases f with
  | domainLive d => rfl
  | valueFact p vf =>
    change (∃ l r, (coarse s).occupancy l = .live r ∧ r.place = p ∧ r.currentFact = vf) ↔
      (∃ l ∈ s.liveRoots, (s.root l).place = p ∧ (s.root l).currentFact = vf)
    simp only [coarse_live]
    constructor
    · rintro ⟨l,r,⟨live,rfl⟩,pe,fe⟩; exact ⟨l,live,pe,fe⟩
    · rintro ⟨l,live,pe,fe⟩; exact ⟨l,coarseRoot (s.root l),⟨live,rfl⟩,pe,fe⟩

theorem coarse_wellFormed {s : Conditional.State} (wf : Conditional.WellFormed s) :
    F0.WellFormed (coarse s) := by
  constructor
  · intro p a b ha hb
    cases a with
    | loose =>
      cases b with
      | loose => rfl
      | installed l =>
        rcases hb with ⟨r,live,pkg⟩
        rcases coarse_live.mp live with ⟨member,rfl⟩
        exact False.elim (wf.frame.installedNotLoose l member (by simpa [← pkg,coarseRoot,Carries,coarse] using ha))
    | installed l =>
      rcases ha with ⟨r,live,pkg⟩
      rcases coarse_live.mp live with ⟨member,rfl⟩
      cases b with
      | loose => exact False.elim (wf.frame.installedNotLoose l member (by simpa [← pkg,coarseRoot,Carries,coarse] using hb))
      | installed m =>
        rcases hb with ⟨q,mlive,mpkg⟩
        rcases coarse_live.mp mlive with ⟨mmember,rfl⟩
        exact congrArg Carrier.installed (wf.frame.installedUnique l member m mmember (pkg.trans mpkg.symm))
  · intro l m r q lr mq eq
    rcases coarse_live.mp lr with ⟨lm,rfl⟩
    rcases coarse_live.mp mq with ⟨mm,rfl⟩
    exact wf.frame.placesUnique l lm m mm eq
  · intro l m r q lr mq eq
    rcases coarse_live.mp lr with ⟨lm,rfl⟩
    rcases coarse_live.mp mq with ⟨mm,rfl⟩
    exact wf.frame.incarnationsUnique l lm m mm eq
  · intro p carrier
    rcases wf.present p (coarse_survives.mp carrier) with ⟨v,data⟩
    exact ⟨⟨Conditional.projectFacts v.dependencies,v.discardable s⟩,by simp [coarse,data]⟩
  · intro l r live
    rcases coarse_live.mp live with ⟨member,rfl⟩
    exact wf.frame.domainsValid l member
  · intro p v carrier data f dep
    rcases Option.map_eq_some_iff.mp data with ⟨rich,richData,rfl⟩
    exact coarse_live_facts.mpr (wf.dependencies p (coarse_survives.mp carrier) rich richData _
      (Conditional.projectFacts_membership.mp dep))
  · intro l r live
    rcases coarse_live.mp live with ⟨member,rfl⟩
    exact wf.frame.valueFactsRecorded l member
  · intro l r live
    rcases coarse_live.mp live with ⟨member,rfl⟩
    exact wf.frame.incarnationsRecorded l member
  · exact wf.frame.domainCarrierCoherent

theorem remaining_was_surviving {s : Conditional.State} {l returned p}
    (live : l ∈ s.liveRoots) (member : p ∈ remainingCarriers s l returned) :
    Conditional.Survives s p := by
  cases returned
  · exact Or.inl (Finset.mem_of_mem_erase member)
  · rcases Finset.mem_insert.mp member with rfl|loose
    · exact Or.inr ⟨l,live,rfl⟩
    · exact Or.inl loose

theorem live_not_ended_remains_live {s : Conditional.State} {l returned f}
    (single : s.liveRoots = {l}) (before : f ∈ Conditional.LiveFacts s)
    (allowed : ¬ Ended (s.root l) f) :
    f ∈ Conditional.LiveFacts (endSemantic s l returned) := by
  cases f with
  | fixed f =>
    cases f with
    | domainLive d => exact before
    | valueFact p vf =>
      rcases before with ⟨m,ml,pe,fe⟩
      have eq : m = l := by simpa [single] using ml
      subst m
      exact False.elim (allowed ⟨pe.symm,fe.symm⟩)
  | occurrence o =>
    rcases before with ⟨m,ml,oe⟩
    have eq : m = l := by simpa [single] using ml
    subst m; exact False.elim (allowed oe)
  | payloadValue o vf =>
    rcases before with ⟨m,ml,oe,fe⟩
    have eq : m = l := by simpa [single] using ml
    subst m; exact False.elim (allowed ⟨oe,fe⟩)

theorem end_semantic_invariant {s : Conditional.State} {l returned}
    (wf : Conditional.Invariant s) (live : l ∈ s.liveRoots) :
    Conditional.Invariant (endSemantic s l returned) := by
  have prior : ∀ p, Conditional.Survives (endSemantic s l returned) p → Conditional.Survives s p := by
    intro p carrier
    rcases carrier with loose|⟨m,ml,_⟩
    · exact remaining_was_surviving live loose
    · simp [endSemantic] at ml
  constructor
  · constructor
    all_goals first
      | exact wf.frame.domainCarrierCoherent
      | intros; simp_all [endSemantic]
  · intro p carrier; exact wf.present p (prior p carrier)
  · intro p carrier v data; exact wf.typed p (prior p carrier) v data
  · intros; simp_all [endSemantic]
  · intros; simp_all [endSemantic]
  · intros; simp_all [endSemantic]
  · intros; simp_all [endSemantic]
  · intros; simp_all [endSemantic]
  · intros; simp_all [endSemantic]

theorem end_semantic_wellFormed {s : Conditional.State} {l returned}
    (wf : Conditional.WellFormed s) (single : s.liveRoots = {l})
    (guard : SurvivorGuard s l returned) : Conditional.WellFormed (endSemantic s l returned) := by
  have live : l ∈ s.liveRoots := by simp [single]
  have prior : ∀ p, Conditional.Survives (endSemantic s l returned) p → Conditional.Survives s p := by
    intro p carrier
    rcases carrier with loose|⟨m,ml,_⟩
    · exact remaining_was_surviving live loose
    · simp [endSemantic] at ml
  refine ⟨end_semantic_invariant wf.toInvariant live,?_⟩
  intro p carrier v data f dep
  have remaining : p ∈ remainingCarriers s l returned := by
    rcases carrier with loose|⟨m,ml,_⟩
    · exact loose
    · simp [endSemantic] at ml
  exact live_not_ended_remains_live single (wf.dependencies p (prior p carrier) v data f dep)
    (guard p remaining v data f dep)

theorem end_all_facts_dead (s : Conditional.State) (l : RootLocationId) (returned : Bool)
    {f} (ended : Ended (s.root l) f) : f ∉ Conditional.LiveFacts (endSemantic s l returned) := by
  cases f with
  | fixed f =>
    cases f with
    | domainLive d => exact False.elim ended
    | valueFact p vf =>
      change ¬ ∃ m ∈ (∅ : Finset RootLocationId), _
      simp
  | occurrence o =>
    change ¬ ∃ m ∈ (∅ : Finset RootLocationId), _
    simp
  | payloadValue o vf =>
    change ¬ ∃ m ∈ (∅ : Finset RootLocationId), _
    simp

theorem end_placement_empty {g layout s l source result t e d ptr ce}
    (wf : SumWellFormed g layout s) (input : EndingInput ce s l source result t e d ptr) :
    ∀ m, (endPlacement s.base.physical l).placement m = none := by
  intro m
  by_cases eq : m = l
  · simp [endPlacement,eq]
  · have dead : m ∉ s.base.semantic.liveRoots := by simp [input.singleRoot,eq]
    have notPlaced := (accounting_derives_physical_wellFormed wf.accounting).exact m
    have empty : s.base.physical.placement m = none := by
      cases h : s.base.physical.placement m with
      | none => rfl
      | some pl => exact False.elim (dead (notPlaced.mpr ⟨pl,h⟩))
    simp [endPlacement,eq,empty]

/-- All accounting post fields are derived, including coverage and disjointness. -/
theorem end_accounting {g layout s l source result t e d ptr ce returned}
    (wf : SumWellFormed g layout s) (input : EndingInput ce s l source result t e d ptr) :
    Accounting g layout (fun m => m ∈ (endCandidate s l source result t e returned).base.semantic.liveRoots)
      (endCandidate s l source result t e returned).base.physical
      (endCandidate s l source result t e returned).ledger := by
  have active : (consumeOne s.ledger source result (.slot t e)).active = {result} := by
    simp [consumeOne,input.singleClaim]
  have data : (consumeOne s.ledger source result (.slot t e)).claim result = .slot t e := by
    simp [consumeOne]
  refine ⟨?_,?_,?_⟩
  · constructor
    · exact wf.accounting.geometry
    · exact wf.accounting.regions
    · exact wf.accounting.scopeLive
    · intro i ia; have eq : i = result := by simpa [endCandidate,active] using ia
      subst i; simpa [endCandidate,data,input.sourceClaim.2,consumeOne,Claim.extent] using wf.accounting.inScope source input.sourceClaim.1
    · intro i ia; have eq : i = result := by simpa [endCandidate,active] using ia
      subst i; simpa [endCandidate,data,input.sourceClaim.2,consumeOne,Claim.extent] using wf.accounting.positive source input.sourceClaim.1
    · intro i ia; have eq : i = result := by simpa [endCandidate,active] using ia
      subst i; simpa [endCandidate,data,input.sourceClaim.2,consumeOne,Claim.extent] using wf.accounting.fits source input.sourceClaim.1
    · intro i ia; have eq : i = result := by simpa [endCandidate,active] using ia
      subst i; simpa [endCandidate,data,input.sourceClaim.2,Claim.Typed] using
        wf.accounting.typed source input.sourceClaim.1
    · intro m; constructor
      · intro ml; simp [endCandidate,endSemantic] at ml
      · rintro ⟨i,ia,u,f,claim⟩
        have eq : i = result := by simpa [endCandidate,active] using ia
        subst i; simp [endCandidate,data] at claim
    · intro m pl; constructor
      · intro placed; have empty := end_placement_empty wf input m
        simp [endCandidate,empty] at placed
      · rintro ⟨i,ia,u,f,claim,_⟩
        have eq : i = result := by simpa [endCandidate,active] using ia
        subst i; simp [endCandidate,data] at claim
  · intro a aa b ba neq
    have ae : a = result := by simpa [endCandidate,active] using aa
    have be : b = result := by simpa [endCandidate,active] using ba
    exact False.elim (neq (ae.trans be.symm))
  · change TotalFootprint g (consumeOne s.ledger source result (.slot t e)) = _
    rw [consumeOne_conserves_footprint g input.sourceClaim.1 input.resultFresh]
    · exact wf.accounting.coverage
    · rw [input.sourceClaim.2]; rfl

theorem end_candidate_wellFormed {g layout s l source result t e d ptr ce returned}
    (wf : SumWellFormed g layout s) (input : EndingInput ce s l source result t e d ptr)
    (guard : SurvivorGuard s.base.semantic l returned) :
    SumWellFormed g layout (endCandidate s l source result t e returned) :=
  let sem := end_semantic_wellFormed (sum_wellFormed_erases_to_conditional wf) input.singleRoot guard
  ⟨sem.toInvariant,sem.dependencies,end_accounting wf input⟩

theorem take_preserves_wellFormed {g layout ce s l source result t e d ptr post}
    (step : TakeStep g layout ce s l source result t e d ptr post) : SumWellFormed g layout post := by
  rw [step.2.1.post_eq]; exact end_candidate_wellFormed step.1 step.2.1.input step.2.2

theorem destroy_preserves_wellFormed {g layout ce s l source result t e d ptr post}
    (step : DestroyStep g layout ce s l source result t e d ptr post) : SumWellFormed g layout post := by
  rw [step.2.1.post_eq]; exact end_candidate_wellFormed step.1 step.2.1.input step.2.2

theorem end_preserves_value_and_history (s : F1.Occupancy.SumState) (l source result t e returned) :
    let post := endCandidate s l source result t e returned
    post.base.semantic.values = s.base.semantic.values ∧
    post.base.semantic.usedValueFacts = s.base.semantic.usedValueFacts ∧
    post.base.semantic.usedIncarnations = s.base.semantic.usedIncarnations ∧
    post.base.semantic.usedOccurrences = s.base.semantic.usedOccurrences ∧
    post.base.semantic.liveDomains = s.base.semantic.liveDomains ∧
    post.base.physical.world = s.base.physical.world := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem take_returns_unique_loose {g layout ce s l source result t e d ptr post}
    (step : TakeStep g layout ce s l source result t e d ptr post) :
    (s.base.semantic.root l).package ∈ post.base.semantic.loosePackages ∧
    ∀ m, m ∉ post.base.semantic.liveRoots := by
  rw [step.2.1.post_eq]; simp [endCandidate,endSemantic,remainingCarriers]

theorem destroy_old_package_not_surviving {ce s l source result t e d ptr post}
    (raw : RawDestroy ce s l source result t e d ptr post) :
    ¬ Conditional.Survives post.base.semantic (s.base.semantic.root l).package := by
  rw [raw.post_eq]; simp [Conditional.Survives,endCandidate,endSemantic,remainingCarriers]

theorem end_responsibility {ce s l source result t e d ptr returned}
    (input : EndingInput ce s l source result t e d ptr) :
    let post := endCandidate s l source result t e returned
    source ∉ post.ledger.active ∧ Has post.ledger result (.slot t e) ∧
    post.ledger.active = {result} ∧ post.ledger.scope = s.ledger.scope ∧
    post.base.physical.placement l = none := by
  refine ⟨consumeOne_consumes_source input.sourceClaim.1 input.resultFresh,
    consumeOne_produces_result _ _ _ _,?_,rfl,?_⟩
  · simp [endCandidate,consumeOne,input.singleClaim]
  · simp [endCandidate,endPlacement]

theorem end_footprint_conserved {g ce s l source result t e d ptr returned}
    (input : EndingInput ce s l source result t e d ptr) :
    TotalFootprint g (endCandidate s l source result t e returned).ledger = TotalFootprint g s.ledger := by
  apply consumeOne_conserves_footprint g input.sourceClaim.1 input.resultFresh
  rw [input.sourceClaim.2]; rfl

theorem take_rejects_ended_dependency {g layout ce s l source result t e d ptr post p v f}
    (carrier : p ∈ remainingCarriers s.base.semantic l true)
    (data : s.base.semantic.values p = some v) (dep : f ∈ v.dependencies)
    (ended : Ended (s.base.semantic.root l) f) :
    ¬ TakeStep g layout ce s l source result t e d ptr post :=
  fun step => step.2.2 p carrier v data f dep ended

theorem destroy_rejects_external_ended_dependency {g layout ce s l source result t e d ptr post p v f}
    (carrier : p ∈ remainingCarriers s.base.semantic l false)
    (data : s.base.semantic.values p = some v) (dep : f ∈ v.dependencies)
    (ended : Ended (s.base.semantic.root l) f) :
    ¬ DestroyStep g layout ce s l source result t e d ptr post :=
  fun step => step.2.2 p carrier v data f dep ended

theorem end_rejects_stale_root_token (s : F1.Occupancy.SumState) (l source result t e returned)
    (ptr : AccessPtr) : ¬ CurrentAccessPtr (coarseState (endCandidate s l source result t e returned)).flat ptr := by
  rintro ⟨⟨r,live,_⟩,_⟩
  simp [coarseState,coarse,endCandidate,endSemantic] at live

theorem take_requires_read_and_ending {ce s l source result t e d ptr post}
    (raw : RawTake ce s l source result t e d ptr post) :
    ce ∧ ptr.evidence.access.read = true ∧
    (s.base.physical.world.access ptr.evidence.region).read = true :=
  ⟨raw.input.endingAllowed,raw.read,evidence_cannot_amplify_read raw.input.current.2.1 raw.read⟩

theorem destroy_requires_discard_and_ending {ce s l source result t e d ptr post}
    (raw : RawDestroy ce s l source result t e d ptr post) :
    ce ∧ ∃ v, s.base.semantic.values (s.base.semantic.root l).package = some v ∧
      v.discardable s.base.semantic = true := ⟨raw.input.endingAllowed,raw.discardable⟩

theorem raw_take_returns_exact_slot {ce s l source result t e d ptr post}
    (raw : RawTake ce s l source result t e d ptr post) : Has post.ledger result (.slot t e) := by
  rw [raw.post_eq]; exact (end_responsibility raw.input).2.1

theorem raw_destroy_returns_exact_slot {ce s l source result t e d ptr post}
    (raw : RawDestroy ce s l source result t e d ptr post) : Has post.ledger result (.slot t e) := by
  rw [raw.post_eq]; exact (end_responsibility raw.input).2.1

theorem end_frames_other_locations (s : F1.Occupancy.SumState) (l source result t e returned)
    {m : RootLocationId} (other : m ≠ l) :
    (endCandidate s l source result t e returned).base.physical.placement m = s.base.physical.placement m := by
  simp [endCandidate,endPlacement,other]

theorem coarse_take_candidate (s : Conditional.State) (l : RootLocationId)
    (single : s.liveRoots = {l}) :
    coarse (endSemantic s l true) = F0.takeCandidate (coarse s) l (coarseRoot (s.root l)) := by
  unfold coarse endSemantic F0.takeCandidate coarseRoot
  congr 1
  funext m; by_cases eq : m = l <;> simp [single,eq]

theorem coarse_destroy_candidate (s : Conditional.State) (l : RootLocationId)
    (single : s.liveRoots = {l}) :
    coarse (endSemantic s l false) = F0.destroyCandidate (coarse s) l (coarseRoot (s.root l)) := by
  unfold coarse endSemantic F0.destroyCandidate coarseRoot
  congr 1
  funext m; by_cases eq : m = l <;> simp [single,eq]

theorem coarse_state_wellFormed {g layout s} (wf : SumWellFormed g layout s) :
    F1.Occupancy.WellFormed g layout (coarseState s) := by
  refine ⟨coarse_wellFormed (sum_wellFormed_erases_to_conditional wf),?_⟩
  have liveEq : FlatLive (coarse s.base.semantic) = (fun l => l ∈ s.base.semantic.liveRoots) := by
    funext l; apply propext; simp [FlatLive,coarse_live]
  change Accounting g layout (FlatLive (coarse s.base.semantic)) s.base.physical s.ledger
  rw [liveEq]; exact wf.accounting

theorem raw_take_projects {ce s l source result t e d ptr post}
    (raw : RawTake ce s l source result t e d ptr post) :
    F1.Occupancy.RawTake ce (coarseState s) source result t e l
      (coarseRoot (s.base.semantic.root l)) d ptr (coarseState post) := by
  rw [raw.post_eq]
  refine ⟨raw.input.sourceClaim,raw.input.resultFresh,?_,rfl⟩
  refine ⟨?_,raw.input.token,raw.input.current,raw.read,rfl⟩
  refine ⟨coarse_live.mpr ⟨by simp [raw.input.singleRoot],rfl⟩,
    raw.input.domainMatches,raw.input.endingAllowed,?_⟩
  exact coarse_take_candidate _ _ raw.input.singleRoot

theorem raw_destroy_projects {ce s l source result t e d ptr post}
    (raw : RawDestroy ce s l source result t e d ptr post) :
    F1.Occupancy.RawDestroy ce (coarseState s) source result t e l
      (coarseRoot (s.base.semantic.root l)) d ptr (coarseState post) := by
  rw [raw.post_eq]
  refine ⟨raw.input.sourceClaim,raw.input.resultFresh,?_,rfl⟩
  refine ⟨?_,raw.input.token,raw.input.current,rfl⟩
  refine ⟨coarse_live.mpr ⟨by simp [raw.input.singleRoot],rfl⟩,
    raw.input.domainMatches,raw.input.endingAllowed,?_,?_⟩
  · rcases raw.discardable with ⟨v,data,cap⟩
    exact ⟨⟨Conditional.projectFacts v.dependencies,v.discardable s.base.semantic⟩,
      by simp [coarseState,coarse,coarseRoot,data],cap⟩
  · exact coarse_destroy_candidate _ _ raw.input.singleRoot

theorem rich_take_projects_to_legal_coarse {g layout ce s l source result t e d ptr post}
    (step : TakeStep g layout ce s l source result t e d ptr post) :
    F1.Occupancy.TakeStep g layout ce (coarseState s) source result t e l
      (coarseRoot (s.base.semantic.root l)) d ptr (coarseState post) :=
  ⟨coarse_state_wellFormed step.1,raw_take_projects step.2.1,
    coarse_state_wellFormed (take_preserves_wellFormed step)⟩

theorem rich_destroy_projects_to_legal_coarse {g layout ce s l source result t e d ptr post}
    (step : DestroyStep g layout ce s l source result t e d ptr post) :
    F1.Occupancy.DestroyStep g layout ce (coarseState s) source result t e l
      (coarseRoot (s.base.semantic.root l)) d ptr (coarseState post) :=
  ⟨coarse_state_wellFormed step.1,raw_destroy_projects step.2.1,
    coarse_state_wellFormed (destroy_preserves_wellFormed step)⟩

theorem rich_take_reviewed_erasure_wellFormed {g layout ce s l source result t e d ptr post}
    (step : TakeStep g layout ce s l source result t e d ptr post) :
    F0.WellFormed (F1.eraseToF0 (Conditional.erase post.base.semantic).base) :=
  sum_wellFormed_erases_to_f0 (take_preserves_wellFormed step)

theorem rich_destroy_reviewed_erasure_wellFormed {g layout ce s l source result t e d ptr post}
    (step : DestroyStep g layout ce s l source result t e d ptr post) :
    F0.WellFormed (F1.eraseToF0 (Conditional.erase post.base.semantic).base) :=
  sum_wellFormed_erases_to_f0 (destroy_preserves_wellFormed step)

end
end NewLang.F3.Memory.SumLifetime
