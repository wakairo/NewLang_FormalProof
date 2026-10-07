import NewLang.F1.FixedChange

namespace NewLang.F1.Reference
open F0
noncomputable section

/-- A persistent mathematical token, not an address, ref, or authority. Parent and
child identities are place-owned; path is an opaque semantic projection sequence. -/
structure FieldPtrToken where
  location : RootLocationId
  rootPlace : PlaceId
  rootIncarnation : IncarnationId
  path : List Nat
  place : PlaceId
  incarnation : IncarnationId
  deriving DecidableEq

/-- Construction alone is not safe issuance. No current-value fact is captured. -/
def fieldTokenAt (s : CurrentState) (t : StructuralTarget) : FieldPtrToken :=
  let r := s.base.root t.location
  ⟨t.location, r.layout.root, (r.node r.layout.root).incarnation,
    r.layout.path t.place, t.place, (r.node t.place).incarnation⟩

structure CurrentFieldPtr (s : CurrentState) (ptr : FieldPtrToken) : Prop where
  target_live : LiveNode s.base ptr.location ptr.place
  fixed : ptr.place ≠ ptr.rootPlace
  parent : (s.base.root ptr.location).layout.root = ptr.rootPlace
  root_incarnation : ((s.base.root ptr.location).node ptr.rootPlace).incarnation = ptr.rootIncarnation
  projection : (s.base.root ptr.location).layout.path ptr.place = ptr.path
  incarnation : ((s.base.root ptr.location).node ptr.place).incarnation = ptr.incarnation

/-- Point acquisition only. Access includes all omitted ordinary permissions,
typed provenance/backing obligations; stability is supplied anew for this state. -/
structure RawFieldAcquireRef (hasStableEvidence canAccess : Prop)
    (s : CurrentState) (ptr : FieldPtrToken) (d : DomainId) : Prop where
  current : CurrentFieldPtr s ptr
  governing : (s.base.root ptr.location).governing = d
  stability : hasStableEvidence
  access : canAccess

def FieldAcquireRef (stable access : Prop) (s : CurrentState)
    (ptr : FieldPtrToken) (d : DomainId) : Prop :=
  CurrentWellFormed s ∧ RawFieldAcquireRef stable access s ptr d

theorem token_at_live_field_is_current {s : CurrentState} {t : StructuralTarget}
    (live : LiveNode s.base t.location t.place)
    (fixed : t.place ≠ (s.base.root t.location).layout.root) :
    CurrentFieldPtr s (fieldTokenAt s t) := ⟨live, fixed, rfl, rfl, rfl, rfl⟩

theorem acquire_requires_current_target {stable access s ptr d}
    (h : FieldAcquireRef stable access s ptr d) : CurrentFieldPtr s ptr := h.2.current

theorem acquire_implies_live_child_incarnation {stable access s ptr d}
    (h : FieldAcquireRef stable access s ptr d) : StructuralLiveIncarnation s.base ptr.incarnation :=
  ⟨ptr.location, ptr.place, h.2.current.target_live, h.2.current.incarnation⟩

theorem acquire_implies_live_parent_incarnation {stable access s ptr d}
    (h : FieldAcquireRef stable access s ptr d) : StructuralLiveIncarnation s.base ptr.rootIncarnation := by
  have live := h.2.current.target_live
  refine ⟨ptr.location, ptr.rootPlace, ⟨live.1, ?_⟩, h.2.current.root_incarnation⟩
  rw [← h.2.current.parent]; exact (h.1.structural.trees _ live.1).root_tracked

theorem acquire_implies_live_governing_domain {stable access s ptr d}
    (h : FieldAcquireRef stable access s ptr d) : d ∈ s.base.liveDomains := by
  rw [← h.2.governing]
  exact h.1.structural.domainsValid _ h.2.current.target_live.1

theorem acquire_does_not_mint_access {stable access s ptr d}
    (h : FieldAcquireRef stable access s ptr d) : stable ∧ access := ⟨h.2.stability, h.2.access⟩

theorem acquire_rejects_missing_stability {stable access s ptr d} (missing : ¬ stable) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => missing h.2.stability

theorem acquire_rejects_missing_access {stable access s ptr d} (missing : ¬ access) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => missing h.2.access

theorem acquire_rejects_wrong_path {stable access s ptr d}
    (wrong : (s.base.root ptr.location).layout.path ptr.place ≠ ptr.path) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => wrong h.2.current.projection

theorem acquire_rejects_wrong_incarnation {stable access s ptr d}
    (wrong : ((s.base.root ptr.location).node ptr.place).incarnation ≠ ptr.incarnation) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => wrong h.2.current.incarnation

theorem acquire_rejects_wrong_root_place {stable access s ptr d}
    (wrong : (s.base.root ptr.location).layout.root ≠ ptr.rootPlace) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => wrong h.2.current.parent

theorem acquire_rejects_wrong_root_incarnation {stable access s ptr d}
    (wrong : ((s.base.root ptr.location).node ptr.rootPlace).incarnation ≠ ptr.rootIncarnation) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => wrong h.2.current.root_incarnation

theorem acquire_rejects_wrong_domain {stable access s ptr d}
    (wrong : (s.base.root ptr.location).governing ≠ d) :
    ¬ FieldAcquireRef stable access s ptr d := fun h => wrong h.2.governing

theorem acquire_rejects_wrong_site {stable access s ptr d l}
    (wf : CurrentWellFormed s) (original : LiveNode s.base l ptr.place)
    (wrong : ptr.location ≠ l) : ¬ FieldAcquireRef stable access s ptr d := by
  intro h
  exact wrong (wf.structural.placesUnique _ _ _ h.2.current.target_live original)

theorem acquire_rejects_retargeted_field {stable access s ptr d p}
    (wf : CurrentWellFormed s) (original : LiveNode s.base ptr.location p)
    (originalInc : ((s.base.root ptr.location).node p).incarnation = ptr.incarnation)
    (wrong : ptr.place ≠ p) : ¬ FieldAcquireRef stable access s ptr d := by
  intro h
  exact wrong (wf.structural.incarnationsUnique _ _ _ _ h.2.current.target_live original
    (h.2.current.incarnation.trans originalInc.symm)).2

/-- No source safe ptr issuance before liveness: this theorem requires current
target identity plus evidence, rather than deriving authority from token existence. -/
theorem current_token_can_acquire {stable access s ptr d}
    (wf : CurrentWellFormed s) (current : CurrentFieldPtr s ptr)
    (governing : (s.base.root ptr.location).governing = d)
    (evidence : stable) (allowed : access) : FieldAcquireRef stable access s ptr d :=
  ⟨wf, current, governing, evidence, allowed⟩

theorem field_replace_preserves_current_token {w ty s post t incoming result v fresh ptr}
    (raw : RawStructuralReplace w ty s t incoming result v fresh post)
    (current : CurrentFieldPtr s ptr) : CurrentFieldPtr post ptr := by
  refine ⟨?_, current.fixed, ?_, ?_, ?_, ?_⟩
  · rw [raw.post_eq]; exact current.target_live
  · rw [replace_preserves_layout raw]; exact current.parent
  · rw [replace_preserves_all_incarnations raw]; exact current.root_incarnation
  · rw [replace_preserves_layout raw]; exact current.projection
  · rw [replace_preserves_all_incarnations raw]; exact current.incarnation

theorem field_replace_reacquires_with_post_evidence {w ty s post t incoming result v fresh ptr d stable access}
    (step : StructuralReplaceStep w ty s t incoming result v fresh post)
    (current : CurrentFieldPtr s ptr) (governing : (s.base.root ptr.location).governing = d)
    (evidence : stable) (allowed : access) : FieldAcquireRef stable access post ptr d := by
  apply current_token_can_acquire step.2.2 (field_replace_preserves_current_token step.2.1 current)
  · rw [replace_preserves_governing_domain step.2.1]; exact governing
  · exact evidence
  · exact allowed

/-- Fixed paths and both incarnations are state-owned, even when a sibling changes. -/
theorem field_replace_preserves_token_at {w ty s post t incoming result v fresh q}
    (raw : RawStructuralReplace w ty s t incoming result v fresh post) :
    fieldTokenAt post q = fieldTokenAt s q := by
  unfold fieldTokenAt
  simp only [replace_preserves_layout raw, replace_preserves_all_incarnations raw]

/-- An acquired field ref cannot override the survivor/current-fact legality rule. -/
theorem acquisition_does_not_bypass_current_dependency {w ty stable access s ptr d incoming result v fresh post}
    (acquired : FieldAcquireRef stable access s ptr d)
    (dependency : Fact.valueFact ptr.place ((s.base.root ptr.location).node ptr.place).currentFact ∈
      LocalDeps (s.base.root ptr.location) ptr.place) :
    ¬ StructuralReplaceStep w ty s ⟨ptr.location,ptr.place⟩ incoming result v fresh post :=
  FixedChange.field_replace_rejects_returned_target_dependency acquired.1
    acquired.2.current.target_live dependency

end
end NewLang.F1.Reference
