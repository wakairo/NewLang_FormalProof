import NewLang.F1.Conditional.Transition

namespace NewLang.F1.Conditional
open F0
noncomputable section

theorem fresh_allocation_cannot_reuse_occurrence {s : State} {a : Allocation}
    (fresh : FreshAllocation s a) {vf : ValueFactId} {o : OccurrenceId}
    (allocated : a.payload = some (vf,o)) (used : o ∈ s.usedOccurrences) : False :=
  (fresh.2 vf o allocated).2.2 used

theorem allocation_occurrence_is_fresh {s : State} {a : Allocation}
    (fresh : FreshAllocation s a) {o : OccurrenceId}
    (active : a.payload.map Prod.snd = some o) : FreshOccurrence s o := by
  cases eq : a.payload with
  | none => simp [eq] at active
  | some pair =>
    have same : pair.2 = o := by simpa [eq] using active
    exact same ▸ (fresh.2 pair.1 pair.2 eq).2.2

section Whole
variable {w ty : Prop} {s post : State} {l : RootLocationId} {incoming : PackageId}
  {v : SumValue} {a : Allocation} {returnsOld : Bool}

theorem whole_preserves_wellFormed
    (step : WholeStep w ty s l incoming v a returnsOld post) : WellFormed post := step.2.2

theorem whole_target_equation (raw : RawWhole w ty s l incoming v a returnsOld post) :
    post.root l = installRoot (s.root l) incoming a := by
  classical
  rw [raw.post_eq]; simp [wholeCandidate]

theorem whole_preserves_parent_identity (raw : RawWhole w ty s l incoming v a returnsOld post) :
    (post.root l).place = (s.root l).place ∧
    (post.root l).incarnation = (s.root l).incarnation ∧
    (post.root l).governing = (s.root l).governing ∧
    (post.root l).typeId = (s.root l).typeId := by
  rw [whole_target_equation raw]; exact ⟨rfl,rfl,rfl,rfl⟩

theorem whole_preserves_static_frame (raw : RawWhole w ty s l incoming v a returnsOld post) :
    post.liveRoots = s.liveRoots ∧ post.liveDomains = s.liveDomains ∧
    post.types = s.types ∧ post.usedIncarnations = s.usedIncarnations ∧
    post.domainValueCarrier = s.domainValueCarrier ∧ post.values = s.values := by
  rw [raw.post_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem whole_other_location_unchanged (raw : RawWhole w ty s l incoming v a returnsOld post)
    {m : RootLocationId} (other : m ≠ l) : post.root m = s.root m := by
  rw [raw.post_eq]; simp [wholeCandidate,other]

theorem whole_new_package_installed (raw : RawWhole w ty s l incoming v a returnsOld post) :
    (post.root l).package = incoming ∧ post.values incoming = some (.sum v) := by
  exact ⟨by rw [whole_target_equation raw]; rfl,
    by rw [(whole_preserves_static_frame raw).2.2.2.2.2]; exact raw.incoming_value⟩

theorem whole_new_occurrence_equation (raw : RawWhole w ty s l incoming v a returnsOld post) :
    (post.root l).occurrence = a.payload.map Prod.snd := by
  rw [whole_target_equation raw]; rfl

theorem whole_history_monotone (raw : RawWhole w ty s l incoming v a returnsOld post) :
    s.usedOccurrences ⊆ post.usedOccurrences ∧ s.usedValueFacts ⊆ post.usedValueFacts := by
  rw [raw.post_eq]; exact ⟨Finset.subset_union_left,Finset.subset_union_left⟩

theorem whole_fresh_occurrence_recorded (raw : RawWhole w ty s l incoming v a returnsOld post)
    {vf : ValueFactId} {o : OccurrenceId} (allocation : a.payload = some (vf,o)) :
    FreshOccurrence s o ∧ o ∈ post.usedOccurrences ∧ (post.root l).occurrence = some o := by
  refine ⟨(raw.fresh.2 vf o allocation).2.2,?_,?_⟩
  · rw [raw.post_eq]; simp [wholeCandidate,Allocation.occurrences,allocation]
  · rw [whole_new_occurrence_equation raw]; simp [allocation]

theorem whole_fresh_current_facts_recorded (raw : RawWhole w ty s l incoming v a returnsOld post) :
    a.current ∉ s.usedValueFacts ∧ a.current ∈ post.usedValueFacts ∧
    (post.root l).currentFact = a.current ∧
    (∀ vf o, a.payload = some (vf,o) → vf ∉ s.usedValueFacts ∧ vf ∈ post.usedValueFacts ∧
      (post.root l).payloadFact = some vf ∧ vf ≠ a.current) := by
  refine ⟨raw.fresh.1,?_,?_,?_⟩
  · rw [raw.post_eq]; simp [wholeCandidate,Allocation.facts]
  · rw [whole_target_equation raw]; rfl
  · intro vf o eq
    refine ⟨(raw.fresh.2 vf o eq).1,?_,?_,(raw.fresh.2 vf o eq).2.1⟩
    · rw [raw.post_eq]; simp [wholeCandidate,Allocation.facts,eq]
    · rw [whole_target_equation raw]; simp [installRoot,eq]

/-- Includes same-variant updates: no variant-equality premise exists. -/
theorem whole_old_occurrence_ended (wf : WellFormed s)
    (raw : RawWhole w ty s l incoming v a returnsOld post) {o : OccurrenceId}
    (old : (s.root l).occurrence = some o) : Fact.occurrence o ∉ LiveFacts post := by
  classical
  intro live
  rcases live with ⟨m,mt,active⟩
  have preLive : m ∈ s.liveRoots := by simpa [raw.post_eq,wholeCandidate] using mt
  by_cases same : m = l
  · subst m
    rw [whole_new_occurrence_equation raw] at active
    exact allocation_occurrence_is_fresh raw.fresh active (wf.occurrencesRecorded l raw.target_live o old)
  · rw [whole_other_location_unchanged raw same] at active
    exact same (wf.occurrencesUnique m preLive l raw.target_live o active old)

theorem whole_replace_old_package_survives (raw : RawWhole w ty s l incoming v a true post) :
    (s.root l).package ∈ post.loosePackages ∧ Survives post (s.root l).package := by
  classical
  have loose : (s.root l).package ∈ post.loosePackages := by
    rw [raw.post_eq]; simp [wholeCandidate]
  exact ⟨loose,Or.inl loose⟩

theorem whole_store_old_package_does_not_survive (wf : WellFormed s)
    (raw : RawWhole w ty s l incoming v a false post) : ¬ Survives post (s.root l).package := by
  classical
  have notLoose : (s.root l).package ∉ s.loosePackages :=
    wf.frame.installedNotLoose l raw.target_live
  have incomingDifferent : incoming ≠ (s.root l).package := by
    intro eq; exact notLoose (eq ▸ raw.incoming_loose)
  intro carrier
  rcases carrier with loose | ⟨m,mt,eq⟩
  · rw [raw.post_eq] at loose
    exact notLoose (Finset.mem_erase.mp loose).2
  · have preLive : m ∈ s.liveRoots := by simpa [raw.post_eq,wholeCandidate] using mt
    by_cases same : m = l
    · subst m; rw [whole_target_equation raw] at eq
      exact incomingDifferent eq
    · rw [whole_other_location_unchanged raw same] at eq
      exact same (wf.frame.installedUnique m preLive l raw.target_live eq)

theorem whole_incoming_no_longer_loose (wf : WellFormed s)
    (raw : RawWhole w ty s l incoming v a returnsOld post) : incoming ∉ post.loosePackages := by
  classical
  have neq : incoming ≠ (s.root l).package := by
    intro eq
    have notLoose : (s.root l).package ∉ s.loosePackages := wf.frame.installedNotLoose l raw.target_live
    exact notLoose (eq ▸ raw.incoming_loose)
  rw [raw.post_eq]; cases returnsOld <;> simp [wholeCandidate,neq]

theorem whole_store_requires_static_sum_discardability
    (raw : RawWhole w ty s l incoming v a false post) :
    (s.types (s.root l).typeId).discardable = true := raw.discardable rfl

theorem whole_store_rejects_nonDiscardable_sum
    (nonDiscardable : (s.types (s.root l).typeId).discardable = false) :
    ¬ WholeStoreStep w ty s l incoming v a post := by
  intro step
  have contradictory := step.2.1.discardable rfl
  rw [nonDiscardable] at contradictory
  cases contradictory

/-- Universal survivor rejection, shared by replace, store, and incoming/external cases. -/
theorem whole_rejects_ended_occurrence_in_survivor (wf : WellFormed s)
    (raw : RawWhole w ty s l incoming v a returnsOld post) {o : OccurrenceId}
    (old : (s.root l).occurrence = some o) {pkg : PackageId} {value : SemanticValue}
    (survives : Survives post pkg) (data : post.values pkg = some value)
    (dependency : Fact.occurrence o ∈ value.dependencies) : ¬ WellFormed post := by
  intro postWf
  exact whole_old_occurrence_ended wf raw old
    (postWf.dependencies pkg survives value data _ dependency)

theorem whole_replace_rejects_returned_occurrence_dependency
    {o : OccurrenceId} (old : (s.root l).occurrence = some o) {value : SemanticValue}
    (data : s.values (s.root l).package = some value)
    (dep : Fact.occurrence o ∈ value.dependencies) : ¬ WholeReplaceStep w ty s l incoming v a post := by
  intro step
  apply whole_rejects_ended_occurrence_in_survivor step.1 step.2.1 old
    (whole_replace_old_package_survives step.2.1).2 ?_ dep step.2.2
  rw [(whole_preserves_static_frame step.2.1).2.2.2.2.2]; exact data

theorem whole_rejects_incoming_occurrence_dependency
    {o : OccurrenceId} (old : (s.root l).occurrence = some o)
    (dep : Fact.occurrence o ∈ v.dependencies) : ¬ WholeStep w ty s l incoming v a returnsOld post := by
  intro step
  have installed := whole_new_package_installed step.2.1
  exact whole_rejects_ended_occurrence_in_survivor step.1 step.2.1 old
    (Or.inr ⟨l,by simpa [step.2.1.post_eq,wholeCandidate] using step.2.1.target_live,installed.1⟩) installed.2 dep step.2.2

/-- The returned value is exactly the old value, while its former occurrence is dead. -/
theorem whole_replace_value_transfers_without_occurrence (wf : WellFormed s)
    (raw : RawWhole w ty s l incoming v a true post) {oldValue : SemanticValue}
    (data : s.values (s.root l).package = some oldValue) {o : OccurrenceId}
    (old : (s.root l).occurrence = some o) :
    post.values (s.root l).package = some oldValue ∧
    Survives post (s.root l).package ∧ Fact.occurrence o ∉ LiveFacts post :=
  ⟨by rw [(whole_preserves_static_frame raw).2.2.2.2.2]; exact data,
    (whole_replace_old_package_survives raw).2,whole_old_occurrence_ended wf raw old⟩
end Whole

section Payload
variable {w ty : Prop} {s post : State} {l : RootLocationId} {incoming result : PackageId}
  {old : SumValue} {new : PayloadValue} {cap : Bool} {rf pf : ValueFactId} {ret : Bool}

theorem payload_preserves_wellFormed
    (step : PayloadStep w ty s l incoming result old new cap rf pf ret post) : WellFormed post := step.2.2

theorem payload_preserves_occurrence
    (raw : RawPayload w ty s l incoming result old new cap rf pf ret post) :
    (post.root l).occurrence = (s.root l).occurrence ∧ post.usedOccurrences = s.usedOccurrences := by
  classical
  rw [raw.post_eq]; simp [payloadCandidate]

theorem payload_preserves_parent_identity
    (raw : RawPayload w ty s l incoming result old new cap rf pf ret post) :
    (post.root l).place = (s.root l).place ∧ (post.root l).incarnation = (s.root l).incarnation ∧
    (post.root l).governing = (s.root l).governing ∧ (post.root l).package = (s.root l).package := by
  classical
  rw [raw.post_eq]; simp [payloadCandidate]

theorem payload_installs_new_value
    (raw : RawPayload w ty s l incoming result old new cap rf pf ret post) :
    post.values (post.root l).package = some (.sum {old with payload := some new}) := by
  classical
  rw [raw.post_eq]; simp [payloadCandidate]

theorem payload_occurrence_dependency_remains_live
    (raw : RawPayload w ty s l incoming result old new cap rf pf ret post) {o : OccurrenceId}
    (active : (s.root l).occurrence = some o) : Fact.occurrence o ∈ LiveFacts post := by
  refine ⟨l,?_,(payload_preserves_occurrence raw).1.trans active⟩
  simpa [raw.post_eq,payloadCandidate] using raw.target_live

theorem payload_old_current_fact_dies
    (wf : WellFormed s) (raw : RawPayload w ty s l incoming result old new cap rf pf ret post)
    {o : OccurrenceId} (occ : (s.root l).occurrence = some o) {oldFact : ValueFactId}
    (oldCurrent : (s.root l).payloadFact = some oldFact) :
    Fact.payloadValue o oldFact ∉ LiveFacts post := by
  classical
  intro live
  rcases live with ⟨m,mt,active,current⟩
  have preActive : (s.root m).occurrence = some o := by
    rw [raw.post_eq] at active
    by_cases same : m = l <;> simpa [payloadCandidate,same] using active
  have same := wf.occurrencesUnique m (by simpa [raw.post_eq,payloadCandidate] using mt) l raw.target_live o preActive occ
  subst m
  have eq : pf = oldFact := by simpa [raw.post_eq,payloadCandidate] using current
  exact raw.payload_fresh (eq ▸ wf.payloadFactsRecorded l raw.target_live oldFact oldCurrent)

theorem payload_rejects_surviving_old_value_dependency
    (wf : WellFormed s) (raw : RawPayload w ty s l incoming result old new cap rf pf ret post)
    {o : OccurrenceId} (occ : (s.root l).occurrence = some o) {oldFact : ValueFactId}
    (oldCurrent : (s.root l).payloadFact = some oldFact) {pkg : PackageId} {value : SemanticValue}
    (survives : Survives post pkg) (data : post.values pkg = some value)
    (dep : Fact.payloadValue o oldFact ∈ value.dependencies) : ¬ WellFormed post := by
  intro postWf
  exact payload_old_current_fact_dies wf raw occ oldCurrent (postWf.dependencies pkg survives value data _ dep)

theorem payload_store_requires_static_payload_discardability
    (raw : RawPayload w ty s l incoming result old new cap rf pf false post) :
    (s.types old.typeId).payloadDiscardable old.variant = true :=
  raw.capability_agrees.symm.trans (raw.discardable rfl)

end Payload

section Swap
variable {w ty : Prop} {s post : State} {left right : RootLocationId}
  {lv rv : SumValue} {a b : Allocation}

theorem swap_preserves_wellFormed (step : SwapStep w ty s left right post) : WellFormed post := step.2.2

theorem swap_same_is_identity (raw : RawSwap w ty s left left post) : post = s := by
  cases raw with
  | same => rfl
  | distinct raw => exact False.elim (raw.distinct rfl)

theorem swap_same_preserves_variant_occurrence_history (raw : RawSwap w ty s left left post) :
    post.root = s.root ∧ post.values = s.values ∧ post.usedOccurrences = s.usedOccurrences ∧
    post.usedValueFacts = s.usedValueFacts := by rw [swap_same_is_identity raw]; exact ⟨rfl,rfl,rfl,rfl⟩

theorem swap_distinct_target_equations (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    post.root left = installRoot (s.root left) (s.root right).package a ∧
    post.root right = installRoot (s.root right) (s.root left).package b := by
  classical
  rw [raw.post_eq]; simp [swapCandidate,Ne.symm raw.distinct]

theorem swap_distinct_preserves_parent_identities (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    (post.root left).place = (s.root left).place ∧
    (post.root right).place = (s.root right).place ∧
    (post.root left).incarnation = (s.root left).incarnation ∧
    (post.root right).incarnation = (s.root right).incarnation ∧
    (post.root left).governing = (s.root left).governing ∧
    (post.root right).governing = (s.root right).governing := by
  rw [(swap_distinct_target_equations raw).1,(swap_distinct_target_equations raw).2]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem swap_distinct_exchanges_values_without_rewriting_dependencies
    (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    post.values = s.values ∧ post.values (post.root left).package = some (.sum rv) ∧
    post.values (post.root right).package = some (.sum lv) := by
  have table : post.values = s.values := by rw [raw.post_eq]; rfl
  rw [table,(swap_distinct_target_equations raw).1,(swap_distinct_target_equations raw).2]
  exact ⟨rfl,raw.right_value,raw.left_value⟩

theorem swap_distinct_preserves_frame (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    post.loosePackages = s.loosePackages ∧ post.liveRoots = s.liveRoots ∧
    post.liveDomains = s.liveDomains ∧ post.domainValueCarrier = s.domainValueCarrier ∧
    post.types = s.types ∧ post.usedIncarnations = s.usedIncarnations := by
  rw [raw.post_eq]; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem swap_distinct_other_location_unchanged (raw : RawSwapDistinct w ty s left right lv rv a b post)
    {m : RootLocationId} (ml : m ≠ left) (mr : m ≠ right) : post.root m = s.root m := by
  rw [raw.post_eq]; simp [swapCandidate,ml,mr]

theorem swap_distinct_both_packages_survive (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    Survives post (s.root left).package ∧ Survives post (s.root right).package := by
  exact ⟨Or.inr ⟨right,by simpa [raw.post_eq,swapCandidate] using raw.right_live,by rw [(swap_distinct_target_equations raw).2]; rfl⟩,
    Or.inr ⟨left,by simpa [raw.post_eq,swapCandidate] using raw.left_live,by rw [(swap_distinct_target_equations raw).1]; rfl⟩⟩

theorem swap_distinct_fresh_occurrences_and_history
    (raw : RawSwapDistinct w ty s left right lv rv a b post)
    {va vb : ValueFactId} {oa ob : OccurrenceId}
    (ae : a.payload = some (va,oa)) (be : b.payload = some (vb,ob)) :
    FreshOccurrence s oa ∧ FreshOccurrence s ob ∧ oa ≠ ob ∧
    (post.root left).occurrence = some oa ∧ (post.root right).occurrence = some ob ∧
    oa ∈ post.usedOccurrences ∧ ob ∈ post.usedOccurrences ∧
    s.usedOccurrences ⊆ post.usedOccurrences ∧ s.usedValueFacts ⊆ post.usedValueFacts := by
  refine ⟨(raw.fresh.1.2 va oa ae).2.2,(raw.fresh.2.1.2 vb ob be).2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · intro same
    have disjoint := Finset.disjoint_left.mp raw.fresh.2.2.2
    exact disjoint (a := oa) (by simp [Allocation.occurrences,ae]) (by simp [Allocation.occurrences,be,same])
  · rw [(swap_distinct_target_equations raw).1]; simp [installRoot,ae]
  · rw [(swap_distinct_target_equations raw).2]; simp [installRoot,be]
  · rw [raw.post_eq]; simp [swapCandidate,Allocation.occurrences,ae]
  · rw [raw.post_eq]; simp [swapCandidate,Allocation.occurrences,be]
  · rw [raw.post_eq]; exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · rw [raw.post_eq]; exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

theorem swap_distinct_old_left_occurrence_ended (wf : WellFormed s)
    (raw : RawSwapDistinct w ty s left right lv rv a b post) {o : OccurrenceId}
    (old : (s.root left).occurrence = some o) : Fact.occurrence o ∉ LiveFacts post := by
  classical
  intro live
  rcases live with ⟨m,mt,active⟩
  have recorded := wf.occurrencesRecorded left raw.left_live o old
  by_cases ml : m = left
  · subst m; rw [(swap_distinct_target_equations raw).1] at active
    exact allocation_occurrence_is_fresh raw.fresh.1 active recorded
  · by_cases mr : m = right
    · subst m; rw [(swap_distinct_target_equations raw).2] at active
      exact allocation_occurrence_is_fresh raw.fresh.2.1 active recorded
    · rw [swap_distinct_other_location_unchanged raw ml mr] at active
      exact ml (wf.occurrencesUnique m (by simpa [raw.post_eq,swapCandidate] using mt) left raw.left_live o active old)

theorem swap_distinct_old_right_occurrence_ended (wf : WellFormed s)
    (raw : RawSwapDistinct w ty s left right lv rv a b post) {o : OccurrenceId}
    (old : (s.root right).occurrence = some o) : Fact.occurrence o ∉ LiveFacts post := by
  classical
  intro live
  rcases live with ⟨m,mt,active⟩
  have recorded := wf.occurrencesRecorded right raw.right_live o old
  by_cases ml : m = left
  · subst m; rw [(swap_distinct_target_equations raw).1] at active
    exact allocation_occurrence_is_fresh raw.fresh.1 active recorded
  · by_cases mr : m = right
    · subst m; rw [(swap_distinct_target_equations raw).2] at active
      exact allocation_occurrence_is_fresh raw.fresh.2.1 active recorded
    · rw [swap_distinct_other_location_unchanged raw ml mr] at active
      exact mr (wf.occurrencesUnique m (by simpa [raw.post_eq,swapCandidate] using mt) right raw.right_live o active old)

theorem swap_rejects_any_surviving_ended_occurrence (wf : WellFormed s)
    (raw : RawSwapDistinct w ty s left right lv rv a b post) {o : OccurrenceId}
    (ended : (s.root left).occurrence = some o ∨ (s.root right).occurrence = some o)
    {pkg : PackageId} {value : SemanticValue} (survives : Survives post pkg)
    (data : post.values pkg = some value) (dep : Fact.occurrence o ∈ value.dependencies) : ¬ WellFormed post := by
  intro postWf
  have live := postWf.dependencies pkg survives value data _ dep
  rcases ended with le|re
  · exact swap_distinct_old_left_occurrence_ended wf raw le live
  · exact swap_distinct_old_right_occurrence_ended wf raw re live

theorem swap_rejects_left_package_occurrence_dependency (wf : WellFormed s)
    (raw : RawSwapDistinct w ty s left right lv rv a b post) {o : OccurrenceId}
    (ended : (s.root left).occurrence = some o ∨ (s.root right).occurrence = some o)
    (dep : Fact.occurrence o ∈ lv.dependencies) : ¬ WellFormed post := by
  apply swap_rejects_any_surviving_ended_occurrence (value := .sum lv) wf raw ended
    (swap_distinct_both_packages_survive raw).1 ?_ dep
  rw [(swap_distinct_exchanges_values_without_rewriting_dependencies raw).1]; exact raw.left_value

theorem swap_rejects_right_package_occurrence_dependency (wf : WellFormed s)
    (raw : RawSwapDistinct w ty s left right lv rv a b post) {o : OccurrenceId}
    (ended : (s.root left).occurrence = some o ∨ (s.root right).occurrence = some o)
    (dep : Fact.occurrence o ∈ rv.dependencies) : ¬ WellFormed post := by
  apply swap_rejects_any_surviving_ended_occurrence (value := .sum rv) wf raw ended
    (swap_distinct_both_packages_survive raw).2 ?_ dep
  rw [(swap_distinct_exchanges_values_without_rewriting_dependencies raw).1]; exact raw.right_value

end Swap
theorem whole_old_root_value_fact_ended {w ty : Prop} {s post : State} {l : RootLocationId}
    {incoming : PackageId} {v : SumValue} {a : Allocation} {ret : Bool}
    (wf : WellFormed s) (raw : RawWhole w ty s l incoming v a ret post) :
    Fact.fixed (.valueFact (s.root l).place (s.root l).currentFact) ∉ LiveFacts post := by
  classical
  intro live
  rcases live with ⟨m,mt,place,current⟩
  have preLive : m ∈ s.liveRoots := by simpa [raw.post_eq,wholeCandidate] using mt
  by_cases same : m = l
  · subst m
    rw [whole_target_equation raw] at current
    change a.current = (s.root l).currentFact at current
    exact raw.fresh.1 (current.symm ▸ wf.frame.valueFactsRecorded l raw.target_live)
  · rw [whole_other_location_unchanged raw same] at place
    exact same (wf.frame.placesUnique m preLive l raw.target_live place)

theorem whole_preserves_erased_fixed_identity {w ty : Prop} {s post : State} {l : RootLocationId}
    {incoming : PackageId} {v : SumValue} {a : Allocation} {ret : Bool}
    (raw : RawWhole w ty s l incoming v a ret post) :
    ((erase post).base.root l).layout = ((erase s).base.root l).layout ∧
    (∀ p, (((erase post).base.root l).node p).incarnation = (((erase s).base.root l).node p).incarnation) := by
  have ids := whole_preserves_parent_identity raw
  exact ⟨by simp only [erase,ids.1],fun _ => ids.2.1⟩

theorem whole_store_requires_all_possible_payload_types_discardable {w ty : Prop}
    {s post : State} {l : RootLocationId} {incoming : PackageId} {v : SumValue} {a : Allocation}
    (raw : RawWhole w ty s l incoming v a false post) :
    ∀ variant ∈ (s.types (s.root l).typeId).variants,
      (s.types (s.root l).typeId).hasPayload variant = true →
      (s.types (s.root l).typeId).payloadDiscardable variant = true := by
  simpa [SumType.discardable] using raw.discardable rfl

theorem payload_fresh_facts_and_history {w ty : Prop} {s post : State} {l : RootLocationId}
    {incoming result : PackageId} {old : SumValue} {new : PayloadValue} {cap ret : Bool}
    {rf pf : ValueFactId}
    (raw : RawPayload w ty s l incoming result old new cap rf pf ret post) :
    rf ∉ s.usedValueFacts ∧ pf ∉ s.usedValueFacts ∧ rf ≠ pf ∧
    rf ∈ post.usedValueFacts ∧ pf ∈ post.usedValueFacts ∧
    s.usedValueFacts ⊆ post.usedValueFacts ∧ post.usedOccurrences = s.usedOccurrences := by
  rw [raw.post_eq]
  exact ⟨raw.root_fresh,raw.payload_fresh,raw.facts_distinct,by simp [payloadCandidate],
    by simp [payloadCandidate],fun _ h=>Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h),rfl⟩

theorem payload_store_rejects_nonDiscardable_payload {w ty : Prop} {s post : State}
    {l : RootLocationId} {incoming result : PackageId} {old : SumValue} {new : PayloadValue}
    {cap : Bool} {rf pf : ValueFactId} (nonDiscardable : cap = false) :
    ¬ PayloadStep w ty s l incoming result old new cap rf pf false post := by
  intro step
  have enabled := step.2.1.discardable rfl
  rw [nonDiscardable] at enabled
  cases enabled

theorem swap_distinct_two_current_facts_fresh_distinct_recorded {w ty : Prop}
    {s post : State} {left right : RootLocationId} {lv rv : SumValue} {a b : Allocation}
    (raw : RawSwapDistinct w ty s left right lv rv a b post) :
    a.current ∉ s.usedValueFacts ∧ b.current ∉ s.usedValueFacts ∧ a.current ≠ b.current ∧
    (post.root left).currentFact = a.current ∧ (post.root right).currentFact = b.current ∧
    a.current ∈ post.usedValueFacts ∧ b.current ∈ post.usedValueFacts ∧
    s.usedValueFacts ⊆ post.usedValueFacts ∧ s.usedOccurrences ⊆ post.usedOccurrences := by
  refine ⟨raw.fresh.1.1,raw.fresh.2.1.1,?_,?_,?_,?_,?_,?_,?_⟩
  · intro eq
    have disjoint := Finset.disjoint_left.mp raw.fresh.2.2.1
    exact disjoint (a := a.current)
      (by simp [Allocation.facts]) (by simp [Allocation.facts,eq])
  · rw [(swap_distinct_target_equations raw).1]; rfl
  · rw [(swap_distinct_target_equations raw).2]; rfl
  · rw [raw.post_eq]; simp [swapCandidate,Allocation.facts]
  · rw [raw.post_eq]; simp [swapCandidate,Allocation.facts]
  · rw [raw.post_eq]; exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  · rw [raw.post_eq]; exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

theorem live_occurrence_has_live_enclosing_root_and_domain {s : State}
    (wf : WellFormed s) {o : OccurrenceId} (live : Fact.occurrence o ∈ LiveFacts s) :
    ∃ l ∈ s.liveRoots, (s.root l).occurrence = some o ∧
      (s.root l).governing ∈ s.liveDomains ∧ (s.root l).incarnation ∈ s.usedIncarnations := by
  rcases live with ⟨l,lt,active⟩
  exact ⟨l,lt,active,wf.frame.domainsValid l lt,wf.frame.incarnationsRecorded l lt⟩

theorem conditional_payload_is_not_added_to_fixed_incarnation_support {s : State}
    {l : RootLocationId} {p : PlaceId} (live : F1.LiveNode (erase s).base l p) :
    p = (s.root l).place ∧ (((erase s).base.root l).node p).incarnation = (s.root l).incarnation :=
  ⟨Finset.mem_singleton.mp live.2,rfl⟩

theorem whole_new_occurrence_differs_from_old {w ty : Prop} {s post : State}
    {l : RootLocationId} {incoming : PackageId} {v : SumValue} {a : Allocation} {ret : Bool}
    (wf : WellFormed s) (raw : RawWhole w ty s l incoming v a ret post)
    {old new : OccurrenceId} {vf : ValueFactId} (prior : (s.root l).occurrence = some old)
    (allocation : a.payload = some (vf,new)) : new ≠ old := by
  intro eq
  exact (raw.fresh.2 vf new allocation).2.2 (eq.symm ▸ wf.occurrencesRecorded l raw.target_live old prior)

theorem whole_payloadless_incoming_has_no_occurrence {w ty : Prop} {s post : State}
    {l : RootLocationId} {incoming : PackageId} {v : SumValue} {a : Allocation} {ret : Bool}
    (raw : RawWhole w ty s l incoming v a ret post) (empty : v.payload = none) :
    (post.root l).occurrence = none ∧ (post.root l).payloadFact = none := by
  have shape := raw.shape
  have noneAllocated : a.payload = none := by
    cases eq : a.payload with
    | none => rfl
    | some x => simp [FitsAllocation,eq,empty] at shape
  rw [whole_target_equation raw]
  simp [installRoot,noneAllocated]

end
end NewLang.F1.Conditional
