import NewLang.Declaration.Completion

namespace NewLang.Declaration

private def rank : Ty → Nat
  | .nominal _ => 2
  | .option t => rank t + 1
  | _ => 0

private theorem edge_decreases {h fields a b} (exact : ExactTypes h fields)
    (edge : ValueEdge h fields a b) : rank b < rank a := by
  cases edge with
  | link => rw [exact.1]; simp [rank]
  | payload => rw [exact.2]; simp [rank]
  | option t => simp [rank]

private theorem path_decreases {h fields a b} (exact : ExactTypes h fields)
    (path : Relation.TransGen (ValueEdge h fields) a b) : rank b < rank a := by
  induction path with
  | single edge => exact edge_decreases exact edge
  | tail path edge ih => exact Nat.lt_trans (edge_decreases exact edge) ih

theorem selected_shape_has_no_value_cycle {h fields} (exact : ExactTypes h fields) :
    NoValueCycle h fields := fun path => Nat.lt_irrefl _ (path_decreases exact path)

theorem ptr_target_is_not_containment {h fields target t} :
    ¬ ValueEdge h fields (.ptr target) t := by intro edge; cases edge

theorem ptr_barrier_stops_every_nonempty_containment_path {h fields target t} :
    ¬ Relation.TransGen (ValueEdge h fields) (.ptr target) t := by
  intro path
  induction path with
  | single edge => exact ptr_target_is_not_containment edge
  | tail _ _ ih => exact ih

theorem ptr_has_typed_target (h : NominalId) : TargetEdge (.ptr h) (.nominal h) := .ptr h

theorem option_link_reaches_only_the_ptr_barrier {h fields} (exact : ExactTypes h fields) :
    Relation.TransGen (ValueEdge h fields) (.nominal h) (.ptr h) := by
  have first : ValueEdge h fields (.nominal h) (.option (.ptr h)) := by simpa only [exact.1] using (ValueEdge.link (h:=h) (fields:=fields))
  exact .tail (.single first) (.option _)

theorem direct_value_cycle_is_rejected {h fields} (self : fields.link.type = .nominal h) :
    ¬ NoValueCycle h fields := by
  intro safe
  exact safe (.single (by simpa only [self] using (ValueEdge.link (h:=h) (fields:=fields))))

theorem option_without_ptr_barrier_has_value_cycle {h fields}
    (self : fields.link.type = .option (.nominal h)) : ¬ NoValueCycle h fields := by
  intro safe
  exact safe (.tail (.single (by simpa only [self] using (ValueEdge.link (h:=h) (fields:=fields)))) (.option _))

theorem completion_preserves_nominal_identity {s r post} (step : CompleteStep s r post) :
    post.identity = s.identity := by rw [step.2]; rfl

theorem completion_preserves_field_labels {s r post} (step : CompleteStep s r post) :
    post.linkLabel = s.linkLabel ∧ post.payloadLabel = s.payloadLabel := by rw [step.2]; exact ⟨rfl,rfl⟩

theorem completion_commits_exact_fields {s r post} (step : CompleteStep s r post) :
    post.phase = .complete r.fields ∧ r.fields.link.identity = s.linkLabel ∧
    r.fields.payload.identity = s.payloadLabel := by
  exact ⟨by rw [step.2]; rfl,step.1.2.2.2.1,step.1.2.2.2.2.1⟩

theorem completion_rejects_identity_substitution {s r post} (wrong : r.identity ≠ s.identity) :
    ¬ CompleteStep s r post := fun step => wrong step.1.2.1

theorem completion_rejects_value_cycle {s r post} (cycle : ¬ NoValueCycle s.identity r.fields) :
    ¬ CompleteStep s r post := fun step => cycle step.1.2.2.2.2.2.2

theorem complete_header_cannot_complete_again {s r post fields}
    (complete : s.phase = .complete fields) : ¬ CompleteStep s r post := by
  intro step; have bad := step.1.1; rw [complete] at bad; cases bad

theorem completion_occurs_once {s r post next another} (step : CompleteStep s r post) :
    ¬ CompleteStep post next another := complete_header_cannot_complete_again (completion_commits_exact_fields step).1

theorem incomplete_header_is_not_another_completed_declaration {s : Header} {fields}
    (incomplete : s.phase = .incomplete) : s.phase ≠ .complete fields := by rw [incomplete]; intro bad; cases bad

theorem complete_function_iff_step {s r post} : complete? s r = some post ↔ CompleteStep s r post := by
  classical
  unfold complete? CompleteStep
  split <;> simp_all [eq_comm]

theorem repeated_option_ptr_instantiation_has_exact_type_identity (a b : NominalId) :
    Ty.option (.ptr a) = Ty.option (.ptr b) ↔ a = b := by
  constructor
  · intro same; exact Ty.ptr.inj (Ty.option.inj same)
  · intro same; rw [same]

theorem ptr_capabilities_ignore_target_completion (s : Header) (h : NominalId) (cap : Capability) :
    Derives s cap 0 (.ptr h) := .ptr h

theorem option_composes_any_payload_property {s cap n t} (property : Derives s cap n t) :
    Derives s cap (n+1) (.option t) := .option property

theorem option_ptr_capabilities_ignore_target_completion (s : Header) (h : NominalId) (cap : Capability) :
    Derives s cap 1 (.option (.ptr h)) := .option (.ptr h)

theorem incomplete_nominal_property_query_is_rejected {s cap}
    (incomplete : s.phase = .incomplete) : ¬ HasProperty s cap (.nominal s.identity) := by
  rintro ⟨n,proof⟩
  cases proof with
  | nominal _ complete _ _ => simp [committedFields,incomplete] at complete

theorem selected_completion_has_finite_property_derivation {s r post}
    (step : CompleteStep s r post) (cap : Capability) : Derives post cap 2 (.nominal s.identity) := by
  have fields := completion_commits_exact_fields step
  have exact := step.1.2.2.2.2.2.1
  apply Derives.nominal (fields:=r.fields) (n:=1) (m:=0)
  · exact ⟨s,r,step⟩
  · simp [committedFields,completion_preserves_nominal_identity step,fields.1]
  · rw [exact.1]; exact .option (.ptr _)
  · rw [exact.2]; exact .byte

theorem nominal_property_requires_exact_completion {s cap h}
    (property : HasProperty s cap (.nominal h)) :
    (∃ initial request, CompleteStep initial request s) ∧
    ∃ fields, committedFields s h = some fields ∧
      HasProperty s cap fields.link.type ∧ HasProperty s cap fields.payload.type := by
  rcases property with ⟨_,proof⟩
  cases proof with
  | nominal completed data left right => exact ⟨completed,_,data,⟨_,left⟩,⟨_,right⟩⟩

theorem ptr_formation_preserves_runtime {pre target ty post} (formation : PtrFormation pre target ty post) :
    post.runtime = pre.runtime := by rw [formation.2.2]

theorem ptr_formation_does_not_mint_incarnations_or_provenance {pre target ty post}
    (formation : PtrFormation pre target ty post) :
    post.runtime.occupancy = pre.runtime.occupancy ∧
    post.runtime.usedIncarnations = pre.runtime.usedIncarnations ∧
    post.runtime.packages = pre.runtime.packages := by rw [ptr_formation_preserves_runtime formation]; exact ⟨rfl,rfl,rfl⟩

theorem completion_does_not_mint_runtime_objects {pre r post} (step : CompletionInWorld pre r post) :
    post.runtime = pre.runtime ∧ post.runtime.occupancy = pre.runtime.occupancy ∧
    post.runtime.usedIncarnations = pre.runtime.usedIncarnations := by rw [step.2]; exact ⟨rfl,rfl,rfl⟩

theorem incomplete_header_cannot_be_published {s} (incomplete : s.phase = .incomplete) :
    asPublished s = none := by simp [asPublished,incomplete]

private theorem complete_function_none {s r fields} (done : s.phase = .complete fields) :
    complete? s r = none := by
  classical
  unfold complete?
  have notEligible : ¬ Eligible s r := by intro h; have bad := h.1; rw [done] at bad; cases bad
  simp [notEligible]

private theorem stage_after_completion {s r rest fields} (done : s.phase = .complete fields) :
    stage s (r :: rest) = none := by simp [stage,complete_function_none done]

theorem two_completion_requests_fail_staging {s r post another rest}
    (step : CompleteStep s r post) : stage s (r :: another :: rest) = none := by
  simp only [stage,(complete_function_iff_step.mpr step)]
  exact stage_after_completion (completion_commits_exact_fields step).1

theorem unresolved_final_header_cannot_register {s} (incomplete : s.phase = .incomplete) :
    registrationResult s [] = .rejected := by simp [registrationResult,stage,incomplete_header_cannot_be_published incomplete]

theorem failed_registration_keeps_public_snapshot {snapshot s requests}
    (failed : registrationResult s requests = .rejected) : publish snapshot s requests = (snapshot,.rejected) := by
  simp [publish,failed]

theorem duplicate_completion_cannot_publish_partial_success {s r post another rest snapshot}
    (step : CompleteStep s r post) : publish snapshot s (r :: another :: rest) = (snapshot,.rejected) := by
  apply failed_registration_keeps_public_snapshot
  simp [registrationResult,step.1.1,two_completion_requests_fail_staging step]

theorem invalid_completion_keeps_public_snapshot {s r snapshot}
    (invalid : ¬ Eligible s r) : publish snapshot s [r] = (snapshot,.rejected) := by
  classical
  apply failed_registration_keeps_public_snapshot
  simp [registrationResult,stage,complete?,invalid]

theorem exact_completion_can_register {s r post} (step : CompleteStep s r post) :
    registrationResult s [r] = .accepted ⟨s.identity,s.linkLabel,s.payloadLabel,r.fields⟩ := by
  simp [registrationResult,step.1.1,stage,complete_function_iff_step.mpr step,asPublished,step.2,completeCandidate]

theorem already_complete_header_cannot_register {s requests fields}
    (done : s.phase = .complete fields) : registrationResult s requests = .rejected := by
  simp [registrationResult,done]

theorem public_success_has_exact_completed_stage {s requests p}
    (success : registrationResult s requests = .accepted p) :
    ∃ final, stage s requests = some final ∧
      ∃ fields, final.phase = .complete fields ∧
        p = ⟨final.identity,final.linkLabel,final.payloadLabel,fields⟩ := by
  unfold registrationResult at success
  split at success
  · cases staged : stage s requests with
    | none => simp [staged] at success
    | some final =>
      refine ⟨final,rfl,?_⟩
      cases phase : final.phase with
      | incomplete => simp [staged,asPublished,phase] at success
      | complete fields =>
        refine ⟨fields,rfl,?_⟩
        simpa [staged,asPublished,phase] using success.symm
  · cases success

theorem public_registration_requires_initial_incomplete_header {s requests p}
    (success : registrationResult s requests = .accepted p) : s.phase = .incomplete := by
  unfold registrationResult at success
  split at success
  · assumption
  · cases success

theorem registration_success_requires_one_exact_completion {s requests p}
    (success : registrationResult s requests = .accepted p) :
    ∃ request post, requests = [request] ∧ CompleteStep s request post := by
  have initial := public_registration_requires_initial_incomplete_header success
  rcases public_success_has_exact_completed_stage success with ⟨final,staged,_,_,_⟩
  cases requests with
  | nil => simp [registrationResult,stage,asPublished,initial] at success
  | cons request rest =>
    cases next : complete? s request with
    | none => simp [stage,next] at staged
    | some post =>
      have step := complete_function_iff_step.mp next
      cases rest with
      | nil => exact ⟨request,post,rfl,step⟩
      | cons another tail =>
        have bad := two_completion_requests_fail_staging (another:=another) (rest:=tail) step
        rw [bad] at staged; cases staged

theorem staging_preserves_nominal_identity {s requests final}
    (staged : stage s requests = some final) : final.identity = s.identity := by
  induction requests generalizing s with
  | nil => simp [stage] at staged; subst final; rfl
  | cons request rest ih =>
    cases next : complete? s request with
    | none => simp [stage,next] at staged
    | some header =>
      have tail : stage header rest = some final := by simpa [stage,next] using staged
      exact (ih tail).trans (completion_preserves_nominal_identity (complete_function_iff_step.mp next))

theorem publication_preserves_nominal_identity {s requests p}
    (success : registrationResult s requests = .accepted p) : p.identity = s.identity := by
  rcases public_success_has_exact_completed_stage success with ⟨final,staged,fields,_,rfl⟩
  exact staging_preserves_nominal_identity staged

theorem publication_commits_exact_selected_types {s requests p}
    (success : registrationResult s requests = .accepted p) : ExactTypes p.identity p.fields := by
  rcases registration_success_requires_one_exact_completion success with ⟨request,post,rfl,step⟩
  have same := Outcome.accepted.inj ((exact_completion_can_register step).symm.trans success)
  rw [← same]
  exact step.1.2.2.2.2.2.1

theorem header_membership {events plan} : plan ∈ headerSet events ↔ Event.declaration plan ∈ events := by
  induction events with
  | nil => simp [headerSet]
  | cons event rest ih =>
    cases event <;> simp_all [headerSet]

theorem header_collection_is_order_independent {xs ys} (permutation : xs.Perm ys) : headerSet xs = headerSet ys := by
  ext plan; rw [header_membership,header_membership]; exact permutation.mem_iff

theorem declaration_occurrence_count_is_order_independent {xs ys} (permutation : xs.Perm ys) :
    headerCount xs = headerCount ys := by
  induction permutation with
  | nil => rfl
  | cons event _ ih => cases event <;> simp [headerCount,ih]
  | swap a b rest => cases a <;> cases b <;> simp [headerCount]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem bounded_admission_is_order_independent {xs ys} (permutation : xs.Perm ys) :
    BoundedCollection xs ↔ BoundedCollection ys := by
  unfold BoundedCollection; rw [declaration_occurrence_count_is_order_independent permutation]

theorem collection_consumer_is_order_independent {xs ys α} (permutation : xs.Perm ys)
    (consumer : Finset Plan → Nat → α) :
    consumer (headerSet xs) (headerCount xs) = consumer (headerSet ys) (headerCount ys) := by
  rw [header_collection_is_order_independent permutation,declaration_occurrence_count_is_order_independent permutation]

end NewLang.Declaration
