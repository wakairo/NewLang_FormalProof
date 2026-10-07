import NewLang.Declaration.Proofs

namespace NewLang.Declaration.Counterexample
noncomputable section

private def node : NominalId := ⟨7⟩
private def other : NominalId := ⟨8⟩
private def header : Header := ⟨node,⟨11⟩,⟨12⟩,.incomplete⟩
private def fields : Fields := ⟨⟨⟨11⟩,.option (.ptr node)⟩,⟨⟨12⟩,.byte⟩⟩
private def request : Request := ⟨node,fields⟩
private def done : Header := completeCandidate header fields
private def plan : Plan := ⟨header,request⟩

private theorem exact_types : ExactTypes node fields := ⟨rfl,rfl⟩

theorem selected_node_shape_is_legal : CompleteStep header request done :=
  ⟨⟨rfl,rfl,by decide,rfl,rfl,exact_types,selected_shape_has_no_value_cycle exact_types⟩,rfl⟩

theorem selected_node_registration_succeeds :
    registrationResult header [request] = .accepted ⟨node,⟨11⟩,⟨12⟩,fields⟩ :=
  exact_completion_can_register selected_node_shape_is_legal

theorem ptr_and_option_properties_exist_before_header_completion :
    (∀ cap, Derives header cap 0 (.ptr node) ∧ Derives header cap 1 (.option (.ptr node))) ∧
    (∀ cap, ¬ HasProperty header cap (.nominal node)) :=
  ⟨fun _cap => ⟨.ptr _, .option (.ptr _)⟩,
    fun _ => incomplete_nominal_property_query_is_rejected rfl⟩

theorem selected_node_copy_and_discardable_have_finite_derivations :
    Derives done .copy 2 (.nominal node) ∧ Derives done .discardable 2 (.nominal node) :=
  ⟨selected_completion_has_finite_property_derivation selected_node_shape_is_legal .copy,
    selected_completion_has_finite_property_derivation selected_node_shape_is_legal .discardable⟩

private def directCycle : Fields := { fields with link := ⟨⟨11⟩,.nominal node⟩ }
private def optionCycle : Fields := { fields with link := ⟨⟨11⟩,.option (.nominal node)⟩ }

theorem direct_by_value_cycle_cannot_complete :
    ¬ NoValueCycle node directCycle ∧ ∀ post, ¬ CompleteStep header ⟨node,directCycle⟩ post :=
  ⟨direct_value_cycle_is_rejected rfl,
    fun _ => completion_rejects_value_cycle (direct_value_cycle_is_rejected rfl)⟩

theorem missing_ptr_barrier_cannot_complete :
    ¬ NoValueCycle node optionCycle ∧ ∀ post, ¬ CompleteStep header ⟨node,optionCycle⟩ post :=
  ⟨option_without_ptr_barrier_has_value_cycle rfl,
    fun _ => completion_rejects_value_cycle (option_without_ptr_barrier_has_value_cycle rfl)⟩

/-- Isolated broken graph merges typed-target and value-containment relations. -/
private def BrokenEdge (a b : Ty) : Prop := ValueEdge node fields a b ∨ TargetEdge a b

theorem treating_ptr_target_as_containment_creates_false_cycle :
    NoValueCycle node fields ∧ Relation.TransGen BrokenEdge (.nominal node) (.nominal node) := by
  refine ⟨selected_shape_has_no_value_cycle exact_types,?_⟩
  exact .tail (.tail (.single (Or.inl ValueEdge.link)) (Or.inl (.option _))) (Or.inr (.ptr _))

theorem selected_path_stops_at_ptr_without_unfolding_header :
    Relation.TransGen (ValueEdge node fields) (.nominal node) (.ptr node) ∧
    ¬ Relation.TransGen (ValueEdge node fields) (.ptr node) (.nominal node) :=
  ⟨option_link_reaches_only_the_ptr_barrier exact_types,ptr_barrier_stops_every_nonempty_containment_path⟩

theorem duplicate_exact_completion_is_rejected :
    (∀ post, ¬ CompleteStep done request post) ∧
    publish none header [request,request] = (none,.rejected) :=
  ⟨fun _ => completion_occurs_once selected_node_shape_is_legal,
    duplicate_completion_cannot_publish_partial_success selected_node_shape_is_legal⟩

theorem inconsistent_second_completion_is_rejected :
    ∀ post, ¬ CompleteStep done ⟨node,directCycle⟩ post :=
  fun _ => completion_occurs_once selected_node_shape_is_legal

theorem different_declaration_cannot_substitute_header_identity :
    ∀ post, ¬ CompleteStep header ⟨other,{ fields with link := ⟨⟨11⟩,.option (.ptr other)⟩ }⟩ post :=
  fun _ => completion_rejects_identity_substitution (by decide)

theorem same_header_cannot_commit_another_nominal_ptr_target :
    ∀ post, ¬ CompleteStep header
      ⟨node,{ fields with link := ⟨⟨11⟩,.option (.ptr other)⟩ }⟩ post := by
  intro post step
  have same := Ty.ptr.inj (Ty.option.inj step.1.2.2.2.2.2.1.1)
  have different : other ≠ node := by decide
  exact different same

theorem duplicate_field_labels_cannot_complete :
    ∀ post, ¬ CompleteStep {header with payloadLabel := ⟨11⟩}
      ⟨node,{ fields with payload := ⟨⟨11⟩,.byte⟩ }⟩ post := by
  intro post step
  exact step.1.2.2.1 rfl

theorem field_order_identity_cannot_be_substituted :
    ∀ post, ¬ CompleteStep header
      ⟨node,⟨⟨⟨12⟩,.option (.ptr node)⟩,⟨⟨11⟩,.byte⟩⟩⟩ post := by
  intro post step
  have bad := step.1.2.2.2.1
  have different : (⟨12⟩ : FieldId) ≠ ⟨11⟩ := by decide
  exact different bad

private def unresolvedRequest : Request := ⟨node,{ fields with payload := ⟨⟨12⟩,.unresolved⟩ }⟩
private theorem unresolved_not_eligible : ¬ Eligible header unresolvedRequest := by
  intro eligible
  have impossible := eligible.2.2.2.2.2.1.2
  cases impossible

theorem unresolved_field_cannot_commit :
    publish none header [unresolvedRequest] = (none,.rejected) :=
  invalid_completion_keeps_public_snapshot unresolved_not_eligible

theorem empty_registration_cannot_publish_incomplete_header :
    publish none header [] = (none,.rejected) :=
  failed_registration_keeps_public_snapshot (unresolved_final_header_cannot_register rfl)

theorem failed_second_completion_preserves_prior_public_snapshot (snapshot : Option Published) :
    stage header [request] = some done ∧
    publish snapshot header [request,request] = (snapshot,.rejected) := by
  refine ⟨?_,duplicate_completion_cannot_publish_partial_success selected_node_shape_is_legal⟩
  simp [stage,complete_function_iff_step.mpr selected_node_shape_is_legal]

private def world : World := ⟨header,F0.State.empty⟩

theorem ptr_type_formation_does_not_create_value_or_provenance :
    PtrFormation world node (.ptr node) world ∧
    world.runtime = F0.State.empty ∧
    (∀ l, world.runtime.occupancy l = .vacant) ∧ world.runtime.usedIncarnations = ∅ :=
  ⟨⟨rfl,rfl,rfl⟩,rfl,fun _ => rfl,rfl⟩

theorem completion_does_not_create_value_or_provenance :
    CompletionInWorld world request ⟨done,F0.State.empty⟩ ∧
    (∀ l, (⟨done,F0.State.empty⟩ : World).runtime.occupancy l = .vacant) ∧
    (⟨done,F0.State.empty⟩ : World).runtime.usedIncarnations = ∅ :=
  ⟨⟨selected_node_shape_is_legal,rfl⟩,fun _ => rfl,rfl⟩

theorem ptr_property_does_not_admit_unknown_type_formation :
    Derives header .copy 0 (.ptr other) ∧ ∀ post, ¬ PtrFormation world other (.ptr other) post := by
  refine ⟨.ptr _,?_⟩
  intro post formation
  have different : other ≠ node := by decide
  exact different formation.1

private def ptrOnly : Fields := { fields with link := ⟨⟨11⟩,.ptr node⟩ }
theorem pointer_only_link_is_not_the_exact_selected_profile :
    ∀ post, ¬ CompleteStep header ⟨node,ptrOnly⟩ post := by
  intro post step
  have wrong := step.1.2.2.2.2.2.1.1
  cases wrong

theorem forged_complete_phase_cannot_skip_registration_validation :
    registrationResult {header with phase := .complete directCycle} [] = .rejected :=
  already_complete_header_cannot_register rfl

private def earlier : List Event := [.declaration plan,.other 0]
private def later : List Event := [.other 0,.declaration plan]
private theorem reordered : earlier.Perm later := List.Perm.swap _ _ _

theorem bounded_header_collection_does_not_depend_on_body_position :
    headerSet earlier = headerSet later ∧ BoundedCollection earlier ∧ BoundedCollection later :=
  ⟨header_collection_is_order_independent reordered,
    by simp [BoundedCollection,earlier,headerCount],by simp [BoundedCollection,later,headerCount]⟩

private def selectedConsumer (plans : Finset Plan) (count : Nat) : Outcome := by
  classical
  exact if plan ∈ plans ∧ count = 1 then registrationResult header [request] else .rejected

theorem bounded_completion_result_does_not_depend_on_body_position :
    selectedConsumer (headerSet earlier) (headerCount earlier) =
      .accepted ⟨node,⟨11⟩,⟨12⟩,fields⟩ ∧
    selectedConsumer (headerSet later) (headerCount later) =
      .accepted ⟨node,⟨11⟩,⟨12⟩,fields⟩ := by
  have same := collection_consumer_is_order_independent reordered selectedConsumer
  have first : selectedConsumer (headerSet earlier) (headerCount earlier) =
      .accepted ⟨node,⟨11⟩,⟨12⟩,fields⟩ := by
    simp [selectedConsumer,earlier,headerSet,headerCount,selected_node_registration_succeeds]
  exact ⟨first,same.symm.trans first⟩

theorem collecting_a_set_alone_would_hide_duplicate_declarations :
    headerSet [.declaration plan,.declaration plan] = headerSet [.declaration plan] ∧
    ¬ BoundedCollection [.declaration plan,.declaration plan] := by
  simp [headerSet,BoundedCollection,headerCount]

end
end NewLang.Declaration.Counterexample
