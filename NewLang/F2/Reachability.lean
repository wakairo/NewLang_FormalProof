import NewLang.F2.Abstract

namespace NewLang.F2
open F0
noncomputable section

inductive Reachable (k : Loop) : ConcreteHeaderState → Prop where
  | entry : Reachable k k.entry
  | backedge {pre post edge} : Reachable k pre → Continue k edge pre post → Reachable k post

/-- Every finite list may use different supplied continue edges. -/
inductive Trace (k : Loop) : ConcreteHeaderState → List Edge → ConcreteHeaderState → Prop where
  | nil (s) : Trace k s [] s
  | cons {s t u i is} : Continue k i s t → Trace k t is u → Trace k s (i :: is) u

def Closed (k : Loop) (h : AbstractHeaderState) : Prop :=
  ∀ s, Represents s h → ∀ i t, Continue k i s t → Represents t h

def PostFixpoint (k : Loop) (h : AbstractHeaderState) : Prop :=
  h.signature = k.signature ∧ Represents k.entry h ∧ Closed k h

theorem entry_reachable (k : Loop) : Reachable k k.entry := .entry

theorem continue_preserves_reachability {k pre post i} (reachable : Reachable k pre)
    (step : Continue k i pre post) : Reachable k post := .backedge reachable step

theorem trace_preserves_representation {k h s t edges} (closed : Closed k h)
    (start : Represents s h) (trace : Trace k s edges t) : Represents t h := by
  induction trace with
  | nil => exact start
  | cons step tail ih => exact ih (closed _ start _ _ step)

theorem arbitrary_finite_continue_sound {k h t edges} (pf : PostFixpoint k h)
    (trace : Trace k k.entry edges t) : Represents t h :=
  trace_preserves_representation pf.2.2 pf.2.1 trace

theorem post_fixpoint_sound {k h s} (pf : PostFixpoint k h) (reachable : Reachable k s) : Represents s h := by
  induction reachable with
  | entry => exact pf.2.1
  | backedge _ step ih => exact pf.2.2 _ ih _ _ step

theorem trace_implies_reachable {k s t edges} (start : Reachable k s) (trace : Trace k s edges t) : Reachable k t := by
  induction trace with
  | nil => exact start
  | cons step _ ih => exact ih (.backedge start step)

theorem trace_append_step {k s t u edges i} (trace : Trace k s edges t) (step : Continue k i t u) :
    Trace k s (edges ++ [i]) u := by
  induction trace with
  | nil => exact .cons step (.nil _)
  | cons first _ ih => exact .cons first (ih step)

theorem reachable_has_finite_trace {k s} (reachable : Reachable k s) : ∃ edges, Trace k k.entry edges s := by
  induction reachable with
  | entry => exact ⟨[],.nil _⟩
  | backedge _ step ih => rcases ih with ⟨edges,trace⟩; exact ⟨_,trace_append_step trace step⟩

/-- State-cover soundness needs neither a least fixed point nor a concrete-ID
enumeration algorithm; this theorem accepts any post-fixpoint. -/
theorem any_inductive_overapproximation_suffices {k h} (pf : PostFixpoint k h) :
    ∀ s, Reachable k s → Represents s h := fun _ reachable => post_fixpoint_sound pf reachable

theorem header_count_and_slot_correspondence {sig s} (wf : HeaderWellFormed sig s) :
    parameterCount s = sig.parameterType.toList.length := by
  rw [← wf.types]; cases eq : s.parameter <;> simp [parameterCount,eq]

theorem represented_exact_layer {s h} (rep : Represents s h) :
    s.parameter.map Package.type = h.signature.parameterType ∧
    s.carriers = expectedCarriers s ∧ s.outerAvailability = h.signature.entryAvailability ∧
    ScopeClosed (survivingDependencies s) := ⟨rep.1.types,rep.1.affine,rep.1.availability,rep.1.scope⟩

namespace Continue
variable {k : Loop} {i : Edge} {pre post : ConcreteHeaderState}

theorem next_binding_fresh (step : Continue k i pre post) :
    post.binding ∉ pre.usedBindings ∧ post.binding ≠ pre.binding :=
  ⟨step.frame.freshBinding,fun eq => step.frame.freshBinding (eq.symm ▸ step.before.bindingRecorded)⟩

theorem outer_availability_exact (step : Continue k i pre post) :
    post.outerAvailability = k.signature.entryAvailability := step.after.availability

theorem no_iteration_dependency_escape (step : Continue k i pre post) (b : BindingId) :
    Dependency.iteration b ∉ survivingDependencies post := step.after.scope b

theorem affine_slot_unique (step : Continue k i pre post) {p : Package} (present : post.parameter = some p) :
    post.carriers = {(post.binding,p.identity)} := by
  rw [step.after.affine]; simp [expectedCarriers,present]

theorem unchanged_transfer_exactly_once (step : Continue k i pre post) {p : Package}
    (before : pre.parameter = some p) (same : post.parameter = pre.parameter) :
    post.carriers = {(post.binding,p.identity)} ∧ (pre.binding,p.identity) ∉ post.carriers := by
  have single := affine_slot_unique step (same.trans before)
  refine ⟨single,?_⟩
  rw [single]; simp [(next_binding_fresh step).2.symm]

theorem transformed_identity_distinct (step : Continue k i pre post) {p q : Package}
    (before : pre.parameter = some p) (fresh : q.identity ∉ pre.usedPackages) : q.identity ≠ p.identity :=
  fun eq => fresh (eq.symm ▸ step.before.packageRecorded p before)

theorem transformed_transfer_exactly_once (step : Continue k i pre post) {p q : Package}
    (before : pre.parameter = some p) (after : post.parameter = some q)
    (fresh : q.identity ∉ pre.usedPackages) :
    post.carriers = {(post.binding,q.identity)} ∧ q.identity ≠ p.identity ∧
    ∀ b, (b,p.identity) ∉ post.carriers := by
  have single := affine_slot_unique step after
  have different := transformed_identity_distinct step before fresh
  refine ⟨single,different,?_⟩
  intro b; rw [single]; simp [different.symm]

theorem histories_monotone (step : Continue k i pre post) :
    pre.usedBindings ⊆ post.usedBindings ∧ pre.usedPackages ⊆ post.usedPackages ∧ pre.usedFacts ⊆ post.usedFacts := by
  refine ⟨by rw [step.frame.bindingHistory]; exact Finset.subset_insert _ _,?_,?_⟩
  · cases step.frame.carry with
    | unchanged _ history => rw [history]
    | transformed p q _ _ _ _ history => rw [history]; exact Finset.subset_insert _ _
  · rcases step.frame.memory with ⟨_,history⟩|⟨_,history⟩
    · rw [history]
    · rw [history]; exact Finset.subset_insert _ _

theorem mutated_current_fact_is_not_live (step : Continue k i pre post)
    (fresh : post.currentFact ∉ pre.usedFacts) :
    ¬ FactLive k.signature post (.externalFact (.valueFact k.signature.outerPlace pre.currentFact)) := by
  rintro (external|current)
  · exact step.after.externalSeparation _ external
  · have eq : pre.currentFact = post.currentFact := F0.Fact.valueFact.inj current |>.2
    exact fresh (eq ▸ step.before.factRecorded)

end Continue
end
end NewLang.F2
