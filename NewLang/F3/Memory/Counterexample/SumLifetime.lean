import NewLang.F3.Memory.Proofs

namespace NewLang.F3.Memory.SumLifetime.Counterexample
open F0 F1 F1.Backing F1.Occupancy
noncomputable section

private def loc : RootLocationId := ⟨0⟩
private def old : PackageId := ⟨0⟩
private def external : PackageId := ⟨1⟩
private def oid : Conditional.OccurrenceId := ⟨0⟩
private def rootFact : Conditional.Fact := .fixed (.valueFact ⟨0⟩ ⟨0⟩)
private def occurrenceFact : Conditional.Fact := .occurrence oid
private def payloadFact : Conditional.Fact := .payloadValue oid ⟨1⟩
private def domainFact : Conditional.Fact := .fixed (.domainLive ⟨0⟩)
private def supported : Finset Conditional.Fact := {rootFact,occurrenceFact,payloadFact,domainFact}
private def sumType (cap : Bool) : Conditional.SumType :=
  ⟨{⟨0⟩,⟨1⟩},fun v => v.index == 1,fun _ => cap⟩
private def value (deps : Finset Conditional.Fact) : Conditional.SemanticValue :=
  .sum ⟨⟨0⟩,⟨1⟩,∅,some ⟨42,deps⟩⟩
private def sem (cap : Bool) (own other : Finset Conditional.Fact) : Conditional.State where
  liveRoots := {loc}
  root := fun _ => ⟨⟨0⟩,⟨0⟩,⟨0⟩,old,⟨0⟩,⟨0⟩,some oid,some ⟨1⟩⟩
  values := fun p => if p = old then some (value own)
    else if p = external then some (.payload ⟨99,other⟩ true) else none
  loosePackages := {external}
  types := fun _ => sumType cap
  liveDomains := {⟨0⟩}
  domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
  usedValueFacts := {⟨0⟩,⟨1⟩,⟨9⟩}
  usedIncarnations := {⟨0⟩,⟨9⟩}
  usedOccurrences := {oid,⟨9⟩}
private def region : BackingRegionId := ⟨0⟩
private def extent : Extent := ⟨region,⟨0,1⟩⟩
private def ty : TypeId := ⟨0⟩
private def source : ClaimId := ⟨0⟩
private def result : ClaimId := ⟨1⟩
private def geometry : Geometry := ⟨fun _ => 1,fun _ n => ⟨n⟩,fun _ _ _ h => congrArg AbstractByteId.index h⟩
private def layout : Layout := ⟨fun _ => 1,fun _ => by decide⟩
private def world (access : Access) : World :=
  ⟨{region},fun r => (Finset.range (geometry.capacity r)).image (geometry.byteAt r),fun _ => access⟩
private def physical (access : Access) : PhysicalState :=
  ⟨world access,fun l => if l = loc then some (extent.placement geometry) else none⟩
private def ledger : Ledger := ⟨{region},{source},fun _ => .root ty loc extent⟩
private def pre (cap : Bool) (own other : Finset Conditional.Fact) (access : Access) : F1.Occupancy.SumState :=
  ⟨⟨sem cap own other,physical access⟩,ledger⟩
private def ptr (access : Access) : AccessPtr := ⟨⟨loc,⟨0⟩⟩,⟨region,access⟩⟩
private def rw : Access := ⟨true,true⟩
private def wo : Access := ⟨false,true⟩
private def after (cap : Bool) (own other : Finset Conditional.Fact) (access : Access) (returned : Bool) :=
  endCandidate (pre cap own other access) loc source result ty extent returned

private theorem semantic_wf (cap : Bool) (own other : Finset Conditional.Fact)
    (validOwn : own ⊆ supported) (validOther : other ⊆ supported) : Conditional.WellFormed (sem cap own other) := by
  have carriers : ∀ p, Conditional.Survives (sem cap own other) p → p = old ∨ p = external := by
    intro p h; rcases h with loose|⟨l,live,eq⟩
    · exact Or.inr (by simpa [sem] using loose)
    · exact Or.inl eq.symm
  have supportedLive : ∀ f ∈ supported, f ∈ Conditional.LiveFacts (sem cap own other) := by
    intro f member
    have cases : f = rootFact ∨ f = occurrenceFact ∨ f = payloadFact ∨ f = domainFact := by
      simpa [supported] using member
    rcases cases with rfl|rfl|rfl|rfl
    · exact ⟨loc,by simp [sem],rfl,rfl⟩
    · exact ⟨loc,by simp [sem],rfl⟩
    · exact ⟨loc,by simp [sem],rfl,rfl⟩
    · change (⟨0⟩ : DomainId) ∈ (sem cap own other).liveDomains; simp [sem]
  refine ⟨?_,?_⟩
  · constructor
    · constructor
      · intro l ll m ml _; have le : l = loc := by simpa [sem] using ll
        have me : m = loc := by simpa [sem] using ml
        exact le.trans me.symm
      · intro l ll m ml _; have le : l = loc := by simpa [sem] using ll
        have me : m = loc := by simpa [sem] using ml
        exact le.trans me.symm
      · intro l ll m ml _; have le : l = loc := by simpa [sem] using ll
        have me : m = loc := by simpa [sem] using ml
        exact le.trans me.symm
      · intro l ll m ml _; have le : l = loc := by simpa [sem] using ll
        have me : m = loc := by simpa [sem] using ml
        exact le.trans me.symm
      · intro l _; simp [sem,old,external]
      · intro l _; simp [sem]
      · intro l _; simp [sem]
      · intro l _; simp [sem]
      · intro d; by_cases eq : d = ⟨0⟩ <;> simp [sem,eq]
    · intro p carrier; rcases carriers p carrier with rfl|rfl <;> simp [sem,old,external]
    · intro p carrier v data
      rcases carriers p carrier with rfl|rfl
      · have eq : v = ⟨⟨0⟩,⟨1⟩,∅,some ⟨42,own⟩⟩ := by
          simpa [Conditional.sumAt,sem,value,Conditional.SemanticValue.sumValue] using data.symm
        subst v; simp [Conditional.ValueTyped,sem,sumType]
      · simp [Conditional.sumAt,sem,old,external,Conditional.SemanticValue.sumValue] at data
    · intro l _ v data
      simpa [Conditional.sumAt,sem,value,Conditional.SemanticValue.sumValue] using congrArg (Option.map Conditional.SumValue.typeId) data.symm
    · intro l _; simp [sem,value]
    · intro l _ v data
      have eq : v = ⟨⟨0⟩,⟨1⟩,∅,some ⟨42,own⟩⟩ := by
        simpa [Conditional.sumAt,sem,value,Conditional.SemanticValue.sumValue] using data.symm
      subst v; simp [sem]
    · intro l ll m ml o _ _
      have le : l = loc := by simpa [sem] using ll
      have me : m = loc := by simpa [sem] using ml
      exact le.trans me.symm
    · intro l _ o eq; have oe : o = oid := by simpa [sem] using eq.symm
      subst o; simp [sem]
    · intro l _ vf eq; have fe : vf = ⟨1⟩ := by simpa [sem] using eq.symm
      subst vf; simp [sem]
  · intro p carrier v data f dep
    rcases carriers p carrier with rfl|rfl
    · have ve : v = value own := by simpa [sem] using data.symm
      subst v
      have mem : f ∈ own := by simpa [value,Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies] using dep
      exact supportedLive f (validOwn mem)
    · have ve : v = .payload ⟨99,other⟩ true := by simpa [sem,old,external] using data.symm
      subst v; exact supportedLive f (validOther dep)

private theorem fixture_accounting (cap : Bool) (own other : Finset Conditional.Fact) (access : Access) :
    Accounting geometry layout (fun l => l ∈ (sem cap own other).liveRoots) (physical access) ledger := by
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro r; rfl
    · intro r rl q ql neq
      have re : r = region := by simpa [physical,world] using rl
      have qe : q = region := by simpa [physical,world] using ql
      exact False.elim (neq (re.trans qe.symm))
    · intro r member; simpa [ledger,physical,world] using member
    · intro i _; simp [ledger,Claim.extent,extent]
    · intro i _; change 0 < 1; decide
    · intro i _; change 1 ≤ 1; decide
    · intro i _; rfl
    · intro l; simp [sem,ledger,eq_comm]
    · intro l pl; by_cases eq : l = loc <;> simp [physical,eq,ledger,eq_comm]
  · intro a aa b ba neq
    have ae : a = source := by simpa [ledger] using aa
    have be : b = source := by simpa [ledger] using ba
    exact False.elim (neq (ae.trans be.symm))
  · simp [TotalFootprint,ExpectedFootprint,ledger,physical,world,Claim.extent,extent,
      Extent.footprint,Range.positions,Range.finish,geometry]

private theorem fixture_wf (cap : Bool) (own other : Finset Conditional.Fact) (access : Access)
    (validOwn : own ⊆ supported) (validOther : other ⊆ supported) :
    SumWellFormed geometry layout (pre cap own other access) :=
  let semantic := semantic_wf cap own other validOwn validOther
  ⟨semantic.toInvariant,semantic.dependencies,fixture_accounting cap own other access⟩

private theorem input (cap : Bool) (own other : Finset Conditional.Fact) (access : Access) :
    EndingInput True (pre cap own other access) loc source result ty extent ⟨0⟩ (ptr access) := by
  refine ⟨rfl,rfl,rfl,⟨by simp [pre,ledger],rfl⟩,by simp [pre,ledger,result,source],
    trivial,rfl,rfl,?_⟩
  refine ⟨⟨coarseRoot ((sem cap own other).root loc),coarse_live.mpr ⟨by simp [pre,sem,ptr],rfl⟩,rfl⟩,
    ⟨by simp [coarseState,pre,physical,world,ptr],accessLe_refl access⟩,extent.placement geometry,?_,rfl⟩
  simp [coarseState,pre,physical,ptr]

private theorem raw_take (cap : Bool) (own other : Finset Conditional.Fact) :
    RawTake True (pre cap own other rw) loc source result ty extent ⟨0⟩ (ptr rw) (after cap own other rw true) :=
  ⟨input _ _ _ _,rfl,rfl⟩

private theorem discardable_true (own other : Finset Conditional.Fact) :
    ∃ v, (sem true own other).values ((sem true own other).root loc).package = some v ∧
      v.discardable (sem true own other) = true := by
  refine ⟨value own,by simp [sem],?_⟩
  simp [value,Conditional.SemanticValue.discardable,Conditional.SumType.discardable,sem,sumType]

private theorem raw_destroy (own other : Finset Conditional.Fact) (access : Access) :
    RawDestroy True (pre true own other access) loc source result ty extent ⟨0⟩ (ptr access)
      (after true own other access false) := ⟨input _ _ _ _,discardable_true own other,rfl⟩

private theorem take_guard (cap : Bool) (own other : Finset Conditional.Fact)
    (onlyOwn : own ⊆ {domainFact}) (onlyOther : other ⊆ {domainFact}) :
    SurvivorGuard (sem cap own other) loc true := by
  intro p member v data f dep
  have cases : p = old ∨ p = external := by simpa [remainingCarriers,sem] using member
  have fact : f = domainFact := by
    rcases cases with rfl|rfl
    · have ve : v = value own := by simpa [sem] using data.symm
      subst v
      exact Finset.mem_singleton.mp (onlyOwn (by
        simpa [value,Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies] using dep))
    · have ve : v = .payload ⟨99,other⟩ true := by simpa [sem,old,external] using data.symm
      subst v; exact Finset.mem_singleton.mp (onlyOther dep)
  subst f; exact not_false

private theorem destroy_guard (own other : Finset Conditional.Fact)
    (onlyOther : other ⊆ {domainFact}) : SurvivorGuard (sem true own other) loc false := by
  intro p member v data f dep
  have pe : p = external := by simpa [remainingCarriers,sem,old,external] using member
  subst p
  have ve : v = .payload ⟨99,other⟩ true := by simpa [sem,old,external] using data.symm
  subst v
  have fe : f = domainFact := Finset.mem_singleton.mp (onlyOther dep)
  subst f; exact not_false

private theorem safe_take (cap : Bool) :
    TakeStep geometry layout True (pre cap {domainFact} {domainFact} rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after cap {domainFact} {domainFact} rw true) := by
  refine ⟨fixture_wf _ _ _ _ ?_ ?_,raw_take _ _ _,take_guard _ _ _ (by rfl) (by rfl)⟩
  all_goals simp [supported]

theorem independent_rich_take_is_legal :
    TakeStep geometry layout True (pre false {domainFact} {domainFact} rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after false {domainFact} {domainFact} rw true) := safe_take false

theorem take_positive_endpoint_and_exact_responsibility :
    SumWellFormed geometry layout (after false {domainFact} {domainFact} rw true) ∧
    old ∈ (after false {domainFact} {domainFact} rw true).base.semantic.loosePackages ∧
    (after false {domainFact} {domainFact} rw true).ledger.active = {result} ∧
    Has (after false {domainFact} {domainFact} rw true).ledger result (.slot ty extent) ∧
    TotalFootprint geometry (after false {domainFact} {domainFact} rw true).ledger = TotalFootprint geometry ledger :=
  ⟨take_preserves_wellFormed (safe_take false),(take_returns_unique_loose (safe_take false)).1,
    (end_responsibility (input false {domainFact} {domainFact} rw)).2.2.1,
    (end_responsibility (input false {domainFact} {domainFact} rw)).2.1,
    end_footprint_conserved (input false {domainFact} {domainFact} rw)⟩

theorem occurrence_payload_root_facts_end :
    occurrenceFact ∉ Conditional.LiveFacts (after false {domainFact} {domainFact} rw true).base.semantic ∧
    payloadFact ∉ Conditional.LiveFacts (after false {domainFact} {domainFact} rw true).base.semantic ∧
    rootFact ∉ Conditional.LiveFacts (after false {domainFact} {domainFact} rw true).base.semantic :=
  ⟨end_all_facts_dead _ _ _ rfl,end_all_facts_dead _ _ _ ⟨rfl,rfl⟩,
    end_all_facts_dead _ _ _ ⟨rfl,rfl⟩⟩

theorem dependency_data_and_retired_history_preserved :
    (after false {domainFact} {domainFact} rw true).base.semantic.values old = some (value {domainFact}) ∧
    (⟨9⟩ : ValueFactId) ∈ (after false {domainFact} {domainFact} rw true).base.semantic.usedValueFacts ∧
    (⟨0⟩ : IncarnationId) ∈ (after false {domainFact} {domainFact} rw true).base.semantic.usedIncarnations ∧
    oid ∈ (after false {domainFact} {domainFact} rw true).base.semantic.usedOccurrences := by
  simp [after,endCandidate,endSemantic,pre,sem]

theorem external_and_fixed_domain_dependency_remain_valid :
    Conditional.Survives (after false {domainFact} {domainFact} rw true).base.semantic external ∧
    domainFact ∈ Conditional.LiveFacts (after false {domainFact} {domainFact} rw true).base.semantic ∧
    Conditional.DependenciesValid (after false {domainFact} {domainFact} rw true).base.semantic := by
  refine ⟨Or.inl ?_,?_,(take_preserves_wellFormed (safe_take false)).dependencies⟩
  · simp [after,endCandidate,endSemantic,remainingCarriers,pre,sem]
  · change (⟨0⟩ : DomainId) ∈ (after false {domainFact} {domainFact} rw true).base.semantic.liveDomains
    simp [after,endCandidate,endSemantic,pre,sem]

private theorem old_take_reject (f : Conditional.Fact) (ended : Ended ((sem true {f} ∅).root loc) f) :
    ¬ TakeStep geometry layout True (pre true {f} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {f} ∅ rw true) := by
  apply take_rejects_ended_dependency (p := old) (v := value {f}) (f := f)
  · simp [remainingCarriers,pre,sem]
  · simp [pre,sem]
  · simp [value,Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies]
  · exact ended

theorem returned_occurrence_dependency_rejects_take :
    SumWellFormed geometry layout (pre true {occurrenceFact} ∅ rw) ∧
    ¬ TakeStep geometry layout True (pre true {occurrenceFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {occurrenceFact} ∅ rw true) := by
  exact ⟨fixture_wf _ _ _ _ (by simp [supported]) (by simp),old_take_reject _ rfl⟩

theorem returned_payload_dependency_rejects_take :
    SumWellFormed geometry layout (pre true {payloadFact} ∅ rw) ∧
    ¬ TakeStep geometry layout True (pre true {payloadFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {payloadFact} ∅ rw true) := by
  exact ⟨fixture_wf _ _ _ _ (by simp [supported]) (by simp),old_take_reject _ ⟨rfl,rfl⟩⟩

theorem returned_root_fact_dependency_rejects_take :
    SumWellFormed geometry layout (pre true {rootFact} ∅ rw) ∧
    ¬ TakeStep geometry layout True (pre true {rootFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {rootFact} ∅ rw true) := by
  exact ⟨fixture_wf _ _ _ _ (by simp [supported]) (by simp),old_take_reject _ ⟨rfl,rfl⟩⟩

theorem destroy_can_consume_old_only_occurrence_dependency :
    DestroyStep geometry layout True (pre true {occurrenceFact} {domainFact} wo) loc source result ty extent
      ⟨0⟩ (ptr wo) (after true {occurrenceFact} {domainFact} wo false) := by
  refine ⟨fixture_wf _ _ _ _ ?_ ?_,raw_destroy _ _ _,destroy_guard _ _ (by rfl)⟩
  all_goals simp [supported]

theorem old_occurrence_dependency_rejects_take_but_allows_destroy :
    ¬ TakeStep geometry layout True (pre true {occurrenceFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {occurrenceFact} ∅ rw true) ∧
    DestroyStep geometry layout True (pre true {occurrenceFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {occurrenceFact} ∅ rw false) :=
  ⟨old_take_reject _ rfl,fixture_wf _ _ _ _ (by simp [supported]) (by simp),raw_destroy _ _ _,
    destroy_guard _ _ (by simp)⟩

theorem external_occurrence_dependency_rejects_take_and_destroy :
    SumWellFormed geometry layout (pre true ∅ {occurrenceFact} rw) ∧
    (¬ TakeStep geometry layout True (pre true ∅ {occurrenceFact} rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true ∅ {occurrenceFact} rw true)) ∧
    ¬ DestroyStep geometry layout True (pre true ∅ {occurrenceFact} rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true ∅ {occurrenceFact} rw false) := by
  refine ⟨fixture_wf _ _ _ _ (by simp) (by simp [supported]),?_,?_⟩
  · apply take_rejects_ended_dependency (p := external) (v := .payload ⟨99,{occurrenceFact}⟩ true) (f := occurrenceFact)
    · simp [remainingCarriers,pre,sem]
    · simp [pre,sem,old,external]
    · simp [Conditional.SemanticValue.dependencies]
    · rfl
  · apply destroy_rejects_external_ended_dependency (p := external) (v := .payload ⟨99,{occurrenceFact}⟩ true) (f := occurrenceFact)
    · simp [remainingCarriers,pre,sem,old,external]
    · simp [pre,sem,old,external]
    · simp [Conditional.SemanticValue.dependencies]
    · rfl

private theorem empty_take :
    TakeStep geometry layout True (pre true ∅ ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true ∅ ∅ rw true) :=
  ⟨fixture_wf _ _ _ _ (by simp) (by simp),raw_take _ _ _,take_guard _ _ _ (by simp) (by simp)⟩

private theorem projected_occurrence_post :
    coarseState (after true {occurrenceFact} ∅ rw true) = coarseState (after true ∅ ∅ rw true) := by
  have semanticEq : coarse (endSemantic (sem true {occurrenceFact} ∅) loc true) =
      coarse (endSemantic (sem true ∅ ∅) loc true) := by
    dsimp [coarse,endSemantic,sem,remainingCarriers]
    congr 1
    funext p
    by_cases eq : p = old <;>
      simp [eq,value,Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies,
        Conditional.projectFacts,occurrenceFact,Conditional.SemanticValue.discardable]
  change (⟨⟨coarse (endSemantic (sem true {occurrenceFact} ∅) loc true),endPlacement (physical rw) loc⟩,
    consumeOne ledger source result (.slot ty extent)⟩ : F1.Occupancy.State) =
    ⟨⟨coarse (endSemantic (sem true ∅ ∅) loc true),endPlacement (physical rw) loc⟩,
    consumeOne ledger source result (.slot ty extent)⟩
  rw [semanticEq]

theorem coarse_legal_take_does_not_imply_rich_legal_take :
    SumWellFormed geometry layout (pre true {occurrenceFact} ∅ rw) ∧
    F1.Occupancy.TakeStep geometry layout True (coarseState (pre true {occurrenceFact} ∅ rw))
      source result ty extent loc (coarseRoot ((sem true {occurrenceFact} ∅).root loc)) ⟨0⟩ (ptr rw)
      (coarseState (after true {occurrenceFact} ∅ rw true)) ∧
    ¬ TakeStep geometry layout True (pre true {occurrenceFact} ∅ rw) loc source result ty extent
      ⟨0⟩ (ptr rw) (after true {occurrenceFact} ∅ rw true) := by
  refine ⟨returned_occurrence_dependency_rejects_take.1,?_,returned_occurrence_dependency_rejects_take.2⟩
  refine ⟨coarse_state_wellFormed returned_occurrence_dependency_rejects_take.1,
    raw_take_projects (raw_take true {occurrenceFact} ∅),?_⟩
  rw [projected_occurrence_post]
  exact coarse_state_wellFormed (take_preserves_wellFormed empty_take)

theorem raw_candidate_has_structure_and_accounting_but_bad_dependencies :
    Conditional.Invariant (after true {occurrenceFact} ∅ rw true).base.semantic ∧
    Accounting geometry layout
      (fun l => l ∈ (after true {occurrenceFact} ∅ rw true).base.semantic.liveRoots)
      (after true {occurrenceFact} ∅ rw true).base.physical
      (after true {occurrenceFact} ∅ rw true).ledger ∧
    ¬ Conditional.DependenciesValid (after true {occurrenceFact} ∅ rw true).base.semantic := by
  refine ⟨end_semantic_invariant returned_occurrence_dependency_rejects_take.1.toInvariant (by simp [pre,sem]),
    end_accounting returned_occurrence_dependency_rejects_take.1 (input _ _ _ _),?_⟩
  intro valid
  have live := valid old (Or.inl (by simp [after,endCandidate,endSemantic,remainingCarriers,pre,sem]))
    (value {occurrenceFact}) (by simp [after,endCandidate,endSemantic,pre,sem]) occurrenceFact
    (by simp [value,Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies])
  exact end_all_facts_dead (sem true {occurrenceFact} ∅) loc true (f := occurrenceFact) rfl live

theorem stale_root_token_rejected_after_both_endings :
    (¬ CurrentAccessPtr (coarseState (after true ∅ ∅ rw true)).flat (ptr rw)) ∧
    ¬ CurrentAccessPtr (coarseState (after true ∅ ∅ rw false)).flat (ptr rw) :=
  ⟨end_rejects_stale_root_token _ _ _ _ _ _ _ _,end_rejects_stale_root_token _ _ _ _ _ _ _ _⟩

theorem take_rejects_missing_read_or_ending :
    (¬ RawTake True (pre true ∅ ∅ wo) loc source result ty extent ⟨0⟩ (ptr wo) (after true ∅ ∅ wo true)) ∧
    ¬ RawTake False (pre true ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) (after true ∅ ∅ rw true) := by
  constructor
  · intro raw; have read := raw.read; cases read
  · intro raw; exact raw.input.endingAllowed

theorem destroy_rejects_missing_discard_or_ending :
    (¬ RawDestroy True (pre false ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) (after false ∅ ∅ rw false)) ∧
    ¬ RawDestroy False (pre true ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) (after true ∅ ∅ rw false) := by
  constructor
  · intro raw
    rcases raw.discardable with ⟨v,data,cap⟩
    have ve : v = value ∅ := by simpa [pre,sem] using data.symm
    subst v
    simp [value,Conditional.SemanticValue.discardable,pre,sem,sumType,Conditional.SumType.discardable] at cap
  · intro raw; exact raw.input.endingAllowed

private def wrongExtent : Extent := ⟨⟨1⟩,⟨0,2⟩⟩
private def wrongSlot : F1.Occupancy.SumState :=
  {after true ∅ ∅ rw true with ledger := consumeOne ledger source result (.slot ty wrongExtent)}

theorem wrong_region_extent_conversion_rejected :
    ¬ RawTake True (pre true ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) wrongSlot := by
  intro raw
  have claim := (raw_take_returns_exact_slot raw).2
  have same : wrongExtent = extent := by simpa [wrongSlot,consumeOne] using claim
  exact (show wrongExtent ≠ extent from by decide) same

private def lost : F1.Occupancy.SumState :=
  {after true ∅ ∅ rw false with ledger := ⟨{region},∅,fun _ => .slot ty extent⟩}
private def duplicated : F1.Occupancy.SumState :=
  {after true ∅ ∅ rw false with ledger := ⟨{region},{source,result},fun _ => .slot ty extent⟩}

theorem missing_responsibility_rejected :
    ¬ SumWellFormed geometry layout lost ∧
    ¬ RawDestroy True (pre true ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) lost := by
  constructor
  · intro wf
    have coverage := wf.accounting.coverage
    have byte : (⟨0⟩ : AbstractByteId) ∈ ExpectedFootprint lost.base.physical lost.ledger := by
      change (⟨0⟩ : AbstractByteId) ∈ (world rw).bytes region; decide
    rw [← coverage] at byte
    simp [TotalFootprint,lost] at byte
  · intro raw
    have claim := (raw_destroy_returns_exact_slot raw).1
    simp [lost] at claim

theorem duplicated_responsibility_rejected :
    ¬ SumWellFormed geometry layout duplicated ∧
    ¬ RawDestroy True (pre true ∅ ∅ rw) loc source result ty extent ⟨0⟩ (ptr rw) duplicated := by
  constructor
  · intro wf
    have overlap := wf.accounting.disjoint source (by simp [duplicated]) result (by simp [duplicated]) (by decide)
    have byte : (⟨0⟩ : AbstractByteId) ∈ extent.footprint geometry := by decide
    exact (Finset.disjoint_left.mp overlap) byte byte
  · intro raw
    have active := (end_responsibility raw.input (returned := false)).2.2.1
    rw [← raw.post_eq] at active
    have mem : source ∈ duplicated.ledger.active := by simp [duplicated]
    rw [active] at mem
    simp [source,result] at mem

end
end NewLang.F3.Memory.SumLifetime.Counterexample
