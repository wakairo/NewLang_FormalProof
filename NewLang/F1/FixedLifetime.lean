import NewLang.F1.Reference

namespace NewLang.F1.FixedLifetime
open F0 Reference
noncomputable section

def rootTarget (s : CurrentState) (l : RootLocationId) : StructuralTarget :=
  ⟨l, (s.base.root l).layout.root⟩

/-- Root end removes the entire live fixed support. Inactive layout/node data is
retained; identities do not become value-owned. Take returns the exact old value,
destroy consumes it atomically. This is a semantic adapter, not Storage geometry. -/
def endCandidate (s : CurrentState) (l : RootLocationId) (returned : Bool) : CurrentState := by
  classical
  let pkg := (s.base.root l).package
  let old := extractValue s (rootTarget s l)
  exact { s with
    base := { s.base with
      liveRoots := s.base.liveRoots.erase l
      loosePackages := if returned then insert pkg s.base.loosePackages else s.base.loosePackages.erase pkg
      looseValues := fun p => if returned = true ∧ p = pkg then some old.summary else s.base.looseValues p }
    carried := fun p => if returned = true ∧ p = pkg then some old else s.carried p }

structure EndingInput (canEnd : Prop) (s : CurrentState) (l : RootLocationId) (d : DomainId) : Prop where
  parent_live : l ∈ s.base.liveRoots
  governing : d = (s.base.root l).governing
  authority : canEnd

structure RawEndRoot (canEnd canReadValue : Prop) (s : CurrentState) (l : RootLocationId)
    (d : DomainId) (returned : Bool) (post : CurrentState) : Prop where
  input : EndingInput canEnd s l d
  read_required : returned = true → canReadValue
  discard_required : returned = false → (s.base.root l).discardable = true
  post_eq : post = endCandidate s l returned

/-- Precisely the dependencies whose carriers survive: other roots, old loose
values, and the returned whole value for take. No post-WellFormed premise. -/
def EndDependenciesSafe (s : CurrentState) (l : RootLocationId) (returned : Bool) : Prop :=
  (∀ m p, LiveNode s.base m p → m ≠ l → ∀ f ∈ LocalDeps (s.base.root m) p,
    f ∈ StructuralLiveFacts (endCandidate s l returned).base) ∧
  (∀ pkg ∈ s.base.loosePackages, ∀ v, s.base.looseValues pkg = some v → ∀ f ∈ v.dependencies,
    f ∈ StructuralLiveFacts (endCandidate s l returned).base) ∧
  (returned = true → ∀ f ∈ (extractValue s (rootTarget s l)).dependencies,
    f ∈ StructuralLiveFacts (endCandidate s l returned).base)

def EndStep (canEnd canReadValue : Prop) (s : CurrentState) (l : RootLocationId)
    (d : DomainId) (returned : Bool) (post : CurrentState) : Prop :=
  CurrentWellFormed s ∧ RawEndRoot canEnd canReadValue s l d returned post ∧
    EndDependenciesSafe s l returned

theorem end_live_node_iff {s l returned m p} :
    LiveNode (endCandidate s l returned).base m p ↔ LiveNode s.base m p ∧ m ≠ l := by
  classical
  simp only [LiveNode,endCandidate,Finset.mem_erase]
  tauto

private theorem end_loose_classification {s l returned pkg}
    (loose : pkg ∈ (endCandidate s l returned).base.loosePackages) :
    (pkg = (s.base.root l).package ∧ returned = true) ∨ pkg ∈ s.base.loosePackages := by
  cases returned with
  | false => exact Or.inr (Finset.mem_of_mem_erase loose)
  | true =>
    rcases Finset.mem_insert.mp loose with eq | old
    · exact Or.inl ⟨eq,rfl⟩
    · exact Or.inr old

theorem end_candidate_wellFormed {s l returned}
    (wf : CurrentWellFormed s) (live : l ∈ s.base.liveRoots)
    (safe : EndDependenciesSafe s l returned) : CurrentWellFormed (endCandidate s l returned) := by
  classical
  let post := endCandidate s l returned
  have looseData : ∀ pkg ∈ post.base.loosePackages, ∃ v,
      post.carried pkg = some v ∧ post.base.looseValues pkg = some v.summary ∧
      ∀ f ∈ v.dependencies, f ∈ StructuralLiveFacts post.base := by
    intro pkg loose
    rcases end_loose_classification loose with ⟨rfl,yes⟩ | old
    · refine ⟨extractValue s (rootTarget s l), ?_, ?_, safe.2.2 yes⟩ <;> simp [post,endCandidate,yes]
    · have different : pkg ≠ (s.base.root l).package := fun eq =>
        wf.structural.installedNotLoose l live (eq ▸ old)
      rcases wf.looseStructured pkg old with ⟨v,value,data⟩
      exact ⟨v, by simpa [post,endCandidate,different] using value,
        by simpa [post,endCandidate,different] using data, safe.2.1 pkg old v.summary data⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro m ml; exact wf.structural.trees m (Finset.mem_of_mem_erase ml)
    · intro m n p mp np; exact wf.structural.placesUnique m n p
        (end_live_node_iff.mp mp).1 (end_live_node_iff.mp np).1
    · intro m p n q mp nq same; exact wf.structural.incarnationsUnique m p n q
        (end_live_node_iff.mp mp).1 (end_live_node_iff.mp nq).1 same
    · intro m p n q mp nq same; exact wf.structural.currentFactsUnique m p n q
        (end_live_node_iff.mp mp).1 (end_live_node_iff.mp nq).1 same
    · intro m ml n nl same; exact wf.structural.installedUnique m (Finset.mem_of_mem_erase ml)
        n (Finset.mem_of_mem_erase nl) same
    · intro m ml loose
      rcases end_loose_classification loose with ⟨eq,_⟩ | old
      · have same := wf.structural.installedUnique m (Finset.mem_of_mem_erase ml) l live eq
        exact (Finset.mem_erase.mp ml).1 same
      · exact wf.structural.installedNotLoose m (Finset.mem_of_mem_erase ml) old
    · intro pkg loose; rcases looseData pkg loose with ⟨v,_,data,_⟩; exact ⟨v.summary,data⟩
    · intro m ml; exact wf.structural.domainsValid m (Finset.mem_of_mem_erase ml)
    · intro m p mp; exact safe.1 m p (end_live_node_iff.mp mp).1 (end_live_node_iff.mp mp).2
    · intro pkg loose value eq f dep
      rcases looseData pkg loose with ⟨v,_,data,valid⟩
      have same : value = v.summary := Option.some.inj (eq.symm.trans data)
      rw [same] at dep
      exact valid f dep
    · intro m p mp; exact wf.structural.valueFactsRecorded m p (end_live_node_iff.mp mp).1
    · intro m p mp; exact wf.structural.incarnationsRecorded m p (end_live_node_iff.mp mp).1
    · exact wf.structural.domainCarrierCoherent
  · intro pkg loose; rcases looseData pkg loose with ⟨v,value,data,_⟩; exact ⟨v,value,data⟩
  · intro m ml; exact wf.rootCapability m (Finset.mem_of_mem_erase ml)

theorem end_preserves_wellFormed {ce read s l d returned post}
    (step : EndStep ce read s l d returned post) : CurrentWellFormed post := by
  rw [step.2.1.post_eq]
  exact end_candidate_wellFormed step.1 step.2.1.input.parent_live step.2.2

theorem end_ends_every_fixed_incarnation {ce read s l d returned post p}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d returned post)
    (tracked : p ∈ (s.base.root l).layout.places) :
    ¬ StructuralLiveIncarnation post.base ((s.base.root l).node p).incarnation := by
  rw [raw.post_eq]
  rintro ⟨m,q,live,same⟩
  have before := (end_live_node_iff.mp live).1
  have sameSite := (wf.structural.incarnationsUnique m q l p before
    ⟨raw.input.parent_live,tracked⟩ same).1
  exact (end_live_node_iff.mp live).2 sameSite

theorem end_ends_every_fixed_current_fact {ce read s l d returned post p}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d returned post)
    (tracked : p ∈ (s.base.root l).layout.places) :
    Fact.valueFact p ((s.base.root l).node p).currentFact ∉ StructuralLiveFacts post.base := by
  rw [raw.post_eq]
  rintro ⟨m,ml,pt,_⟩
  have before := (end_live_node_iff.mp ⟨ml,pt⟩).1
  have sameSite := wf.structural.placesUnique m l p before ⟨raw.input.parent_live,tracked⟩
  exact (end_live_node_iff.mp ⟨ml,pt⟩).2 sameSite

theorem end_rejects_old_field_acquisition {ce read stable access s l d returned post ptr evidenceDomain}
    (raw : RawEndRoot ce read s l d returned post) (site : ptr.location = l) :
    ¬ FieldAcquireRef stable access post ptr evidenceDomain := by
  intro h
  have live := h.2.current.target_live
  rw [raw.post_eq] at live
  exact (end_live_node_iff.mp live).2 site

theorem end_retains_identity_history {ce read s l d returned post}
    (raw : RawEndRoot ce read s l d returned post) :
    post.base.usedIncarnations = s.base.usedIncarnations ∧ post.base.usedValueFacts = s.base.usedValueFacts := by
  rw [raw.post_eq]; exact ⟨rfl,rfl⟩

theorem ended_field_token_remains_recorded {ce read s l d returned post ptr}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d returned post)
    (current : CurrentFieldPtr s ptr) :
    ptr.incarnation ∈ post.base.usedIncarnations := by
  rw [(end_retains_identity_history raw).1, ← current.incarnation]
  exact wf.structural.incarnationsRecorded _ _ current.target_live

/-- A future whole-tree lifetime start must use historically fresh identities at
every tracked position. This is a freshness certificate, not a new initialize op. -/
def FreshTreeRestart (ended restarted : CurrentState) (l : RootLocationId) : Prop :=
  l ∉ ended.base.liveRoots ∧ l ∈ restarted.base.liveRoots ∧
  ended.base.usedIncarnations ⊆ restarted.base.usedIncarnations ∧
  ∀ p ∈ (restarted.base.root l).layout.places,
    ((restarted.base.root l).node p).incarnation ∉ ended.base.usedIncarnations

theorem fresh_tree_restart_rejects_recorded_field_token {ended restarted l ptr stable access d}
    (restart : FreshTreeRestart ended restarted l) (site : ptr.location = l)
    (recorded : ptr.incarnation ∈ ended.base.usedIncarnations) :
    ¬ FieldAcquireRef stable access restarted ptr d := by
  intro h
  have live := h.2.current.target_live
  have same := h.2.current.incarnation
  rw [site] at live same
  exact restart.2.2.2 _ live.2 (same.symm ▸ recorded)

theorem end_then_fresh_restart_rejects_old_field_token {ce read s l d returned ended restarted ptr stable access ed}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d returned ended)
    (current : CurrentFieldPtr s ptr) (site : ptr.location = l)
    (restart : FreshTreeRestart ended restarted l) :
    ¬ FieldAcquireRef stable access restarted ptr ed :=
  fresh_tree_restart_rejects_recorded_field_token restart site
    (ended_field_token_remains_recorded wf raw current)

theorem end_rejects_missing_authority {ce read s l d returned post} (missing : ¬ ce) :
    ¬ RawEndRoot ce read s l d returned post := fun raw => missing raw.input.authority

theorem take_requires_ordinary_read {ce read s l d post}
    (raw : RawEndRoot ce read s l d true post) : read := raw.read_required rfl

theorem destroy_requires_discardability {ce read s l d post}
    (raw : RawEndRoot ce read s l d false post) : (s.base.root l).discardable = true := raw.discard_required rfl

theorem end_preserves_other_node_identity {ce read s l d returned post m p}
    (raw : RawEndRoot ce read s l d returned post) (other : m ≠ l) :
    LiveNode post.base m p ↔ LiveNode s.base m p := by rw [raw.post_eq,end_live_node_iff]; simp [other]

theorem end_preserves_domains {ce read s l d returned post}
    (raw : RawEndRoot ce read s l d returned post) :
    post.base.liveDomains = s.base.liveDomains ∧ post.base.domainValueCarrier = s.base.domainValueCarrier := by
  rw [raw.post_eq]; exact ⟨rfl,rfl⟩

theorem take_returns_exact_value {ce read s l d post}
    (raw : RawEndRoot ce read s l d true post) :
    (s.base.root l).package ∈ post.base.loosePackages ∧
    post.carried (s.base.root l).package = some (extractValue s (rootTarget s l)) ∧
    post.base.looseValues (s.base.root l).package = some (extractValue s (rootTarget s l)).summary := by
  classical
  rw [raw.post_eq]; simp [endCandidate]

theorem destroy_does_not_return_old_value {ce read s l d post}
    (raw : RawEndRoot ce read s l d false post) : (s.base.root l).package ∉ post.base.loosePackages := by
  classical
  rw [raw.post_eq]; simp [endCandidate]

/-- Reuse F0 raw lifetime semantics for the root shadow. This is not full package
table erasure commutation or a coarse-to-rich legality implication. -/
theorem take_has_f0_root_shadow {ce read s l d post}
    (raw : RawEndRoot ce read s l d true post) :
    F0.RawTake ce (eraseToF0 s.base) l (eraseRoot (s.base.root l)) d
      (F0.takeCandidate (eraseToF0 s.base) l (eraseRoot (s.base.root l))) :=
  ⟨(erase_occupancy_live_iff _ _ _).mpr ⟨raw.input.parent_live,rfl⟩,raw.input.governing,
    raw.input.authority,rfl⟩

theorem destroy_has_f0_root_shadow {ce read s l d post}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d false post) :
    F0.RawDestroy ce (eraseToF0 s.base) l (eraseRoot (s.base.root l)) d
      (F0.destroyCandidate (eraseToF0 s.base) l (eraseRoot (s.base.root l))) := by
  refine ⟨(erase_occupancy_live_iff _ _ _).mpr ⟨raw.input.parent_live,rfl⟩,raw.input.governing,
    raw.input.authority, ?_, rfl⟩
  refine ⟨_, erase_root_package_exact wf.structural raw.input.parent_live, ?_⟩
  exact raw.discard_required rfl

theorem take_root_occupancy_commutes_with_erasure {ce read s l d post}
    (raw : RawEndRoot ce read s l d true post) :
    (eraseToF0 post.base).occupancy =
      (F0.takeCandidate (eraseToF0 s.base) l (eraseRoot (s.base.root l))).occupancy := by
  classical
  rw [raw.post_eq]
  funext m
  by_cases same : m = l <;> simp [endCandidate,eraseToF0,F0.takeCandidate,same]

theorem destroy_root_occupancy_commutes_with_erasure {ce read s l d post}
    (raw : RawEndRoot ce read s l d false post) :
    (eraseToF0 post.base).occupancy =
      (F0.destroyCandidate (eraseToF0 s.base) l (eraseRoot (s.base.root l))).occupancy := by
  classical
  rw [raw.post_eq]
  funext m
  by_cases same : m = l <;> simp [endCandidate,eraseToF0,F0.destroyCandidate,same]

theorem take_parent_incarnation_ends_in_erasure {ce read s l d post}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d true post) :
    ¬ F0.LiveIncarnation (eraseToF0 post.base) ((s.base.root l).node (s.base.root l).layout.root).incarnation := by
  rintro ⟨m,root,live,same⟩
  apply F0.take_ends_incarnation (f1_wellFormed_erases_to_f0_wellFormed wf.structural)
    (take_has_f0_root_shadow raw)
  exact ⟨m,root,by rw [← take_root_occupancy_commutes_with_erasure raw]; exact live,same⟩

theorem destroy_parent_incarnation_ends_in_erasure {ce read s l d post}
    (wf : CurrentWellFormed s) (raw : RawEndRoot ce read s l d false post) :
    ¬ F0.LiveIncarnation (eraseToF0 post.base) ((s.base.root l).node (s.base.root l).layout.root).incarnation := by
  rintro ⟨m,root,live,same⟩
  apply F0.destroy_ends_incarnation (f1_wellFormed_erases_to_f0_wellFormed wf.structural)
    (destroy_has_f0_root_shadow wf raw)
  exact ⟨m,root,by rw [← destroy_root_occupancy_commutes_with_erasure raw]; exact live,same⟩

theorem take_rejects_returned_ended_fact_dependency {ce read s l d post p}
    (tracked : p ∈ (s.base.root l).layout.places)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      (extractValue s (rootTarget s l)).dependencies) :
    ¬ EndStep ce read s l d true post := by
  intro step
  have dead := end_ends_every_fixed_current_fact step.1 step.2.1 tracked
  apply dead
  rw [step.2.1.post_eq]
  exact step.2.2.2.2 rfl _ dependency

theorem end_rejects_external_ended_fact_dependency {ce read s l d returned post p m q}
    (tracked : p ∈ (s.base.root l).layout.places) (owner : LiveNode s.base m q)
    (other : m ≠ l)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ LocalDeps (s.base.root m) q) :
    ¬ EndStep ce read s l d returned post := by
  intro step
  apply end_ends_every_fixed_current_fact step.1 step.2.1 tracked
  rw [step.2.1.post_eq]
  exact step.2.2.1 m q owner other _ dependency

theorem end_rejects_loose_ended_fact_dependency {ce read s l d returned post p pkg v}
    (tracked : p ∈ (s.base.root l).layout.places) (loose : pkg ∈ s.base.loosePackages)
    (value : s.base.looseValues pkg = some v)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈ v.dependencies) :
    ¬ EndStep ce read s l d returned post := by
  intro step
  apply end_ends_every_fixed_current_fact step.1 step.2.1 tracked
  rw [step.2.1.post_eq]
  exact step.2.2.2.1 pkg loose v value _ dependency

theorem acquisition_does_not_mint_ending_authority {stable access s ptr evidenceDomain read l d returned post}
    (_acquired : FieldAcquireRef stable access s ptr evidenceDomain) :
    ¬ RawEndRoot False read s l d returned post := end_rejects_missing_authority not_false

end
end NewLang.F1.FixedLifetime
