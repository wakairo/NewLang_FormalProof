import NewLang.F1.FixedLifetime
import NewLang.F1.Backing.Lifetime
import NewLang.F1.Occupancy.Model
import NewLang.Adjunct.SourceRichBoundary

/-!
F64: finite diagnostics at the fixed-child / backing / borrowed-ref boundary.
Verdict: MODEL INCOMPLETE HOLD. This preinitialized F1 witness is not an
Array/Option source issuer, typed None interpretation, or derived child ref.
Root-only physical data are checked separately; no Allocation value is minted.
See docs/F64_ARRAY4_BOUNDARY_REPORT.ja.md for fixed authorities and limits.
-/

namespace NewLang.Adjunct.Array4Boundary
open F0 F1.Reference F1.Backing F1.Occupancy
noncomputable section

def location : RootLocationId := ⟨0⟩
def rootPlace : PlaceId := ⟨0⟩
def domain : DomainId := ⟨0⟩
def child (i : Fin 4) : PlaceId := ⟨i.val+1⟩
def places : Finset PlaceId := (Finset.range 5).image PlaceId.mk
def path (p : PlaceId) : List Nat := if p.index = 0 then [] else [p.index-1]
def layout : F1.StructuralLayout := ⟨places,rootPlace,path⟩

theorem tree : F1.TreeWellFormed layout := by
  constructor
  · simp [layout,places,rootPlace]
  · rfl
  · intro p _ q _ same
    cases p with
    | mk p =>
      cases q with
      | mk q =>
        by_cases hp : p = 0
        · by_cases hq : q = 0
          · subst p; subst q; rfl
          · simp [layout,path,hp,hq] at same
        · by_cases hq : q = 0
          · simp [layout,path,hp,hq] at same
          · have eq : p-1 = q-1 := by simpa [layout,path,hp,hq] using same
            have eqn : p = q := by omega
            subst q; rfl
  · intro p member notRoot
    have nz : p.index ≠ 0 := by
      intro zero; apply notRoot
      cases p with
      | mk n => simp only at zero; subst n; rfl
    exact ⟨rootPlace,by simp [layout,places,rootPlace],p.index-1,by simp [layout,path,nz,rootPlace]⟩

def object : F1.StructuredRoot :=
  ⟨layout,fun p => ⟨⟨p.index⟩,⟨p.index⟩,∅⟩,⟨0⟩,domain,true⟩
/-- A finite abstract state. Content 91 is opaque, not a None tag or byte. -/
def state : F1.CurrentState where
  base := {
    liveRoots := {location}
    root := fun _ => object
    loosePackages := ∅
    looseValues := fun _ => none
    liveDomains := {domain}
    domainValueCarrier := fun d => if d = domain then some ⟨7⟩ else none
    usedValueFacts := places.image (fun p => (⟨p.index⟩ : ValueFactId))
    usedIncarnations := places.image (fun p => (⟨p.index⟩ : IncarnationId)) }
  content := fun _ _ => 91
  capability := fun _ _ => true
  carried := fun _ => none

theorem state_wf : F1.CurrentWellFormed state := by
  refine ⟨?_,by simp [state],fun _ _ => rfl⟩
  constructor
  · intro l _; exact tree
  · intro l m p lp mp; exact (Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mp.1).symm
  · intro l p m q lp mq same
    refine ⟨(Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mq.1).symm,?_⟩
    cases p; cases q; simpa [state,object] using same
  · intro l p m q lp mq same
    refine ⟨(Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mq.1).symm,?_⟩
    cases p; cases q; simpa [state,object] using same
  · intro l ll m ml _; exact (Finset.mem_singleton.mp ll).trans (Finset.mem_singleton.mp ml).symm
  · intro l _; simp [state]
  · simp [state]
  · intro l _; simp [state,object]
  · intro l p live f dep; exact False.elim (Finset.notMem_empty _ dep)
  · simp [state]
  · intro l p live; exact Finset.mem_image.mpr ⟨p,live.2,rfl⟩
  · intro l p live; exact Finset.mem_image.mpr ⟨p,live.2,rfl⟩
  · intro d; by_cases same : d = domain <;> simp [state,same]

theorem child_tracked (i : Fin 4) : child i ∈ layout.places := by
  exact Finset.mem_image.mpr ⟨i.val+1,Finset.mem_range.mpr (by have := i.isLt; omega),rfl⟩

theorem child_not_root (i : Fin 4) : child i ≠ rootPlace := by
  intro eq; have bad := congrArg PlaceId.index eq; simp [child,rootPlace] at bad

def token (i : Fin 4) : FieldPtrToken := fieldTokenAt state ⟨location,child i⟩
theorem current (i : Fin 4) : CurrentFieldPtr state (token i) :=
  token_at_live_field_is_current ⟨by simp [state],child_tracked i⟩ (child_not_root i)

/-- Omitted applicability is retained as an explicit supplied proposition. -/
theorem point_acquisition (i : Fin 4) (access : Prop) (supplied : access) :
    FieldAcquireRef True access state (token i) domain :=
  current_token_can_acquire state_wf (current i) rfl trivial supplied

theorem parent_end_invalidates_all {ce read d returned post}
    (raw : F1.FixedLifetime.RawEndRoot ce read state location d returned post) :
    ∀ i : Fin 4, ¬ FieldAcquireRef True True post (token i) domain := by
  intro i; exact F1.FixedLifetime.end_rejects_old_field_acquisition raw rfl


def region : BackingRegionId := ⟨0⟩
def ro : Access := ⟨true,false⟩
def rw : Access := ⟨true,true⟩
def world : World := ⟨{region},fun _ => (Finset.range 10).image AbstractByteId.mk,fun _ => rw⟩
def parentEvidence : Evidence := ⟨region,ro⟩
def unrelatedEvidence : Evidence := ⟨region,rw⟩
theorem world_bound_is_not_parent_bound :
    EvidenceValid world parentEvidence ∧ EvidenceValid world unrelatedEvidence ∧
    ¬ AccessLe unrelatedEvidence.access parentEvidence.access := by
  constructor
  · exact ⟨by simp [world,parentEvidence],⟨id,by simp [parentEvidence,ro]⟩⟩
  constructor
  · exact ⟨by simp [world,unrelatedEvidence],accessLe_refl _⟩
  · intro le; have no := le.2 rfl; cases no

/-- Ordinal diagnostic ranges only; no Option representation or ABI. -/
def parentExtent : Range := ⟨0,8⟩
def fourthExtent : Range := ⟨6,2⟩
def escapedExtent : Range := ⟨8,2⟩
theorem guessed_extent_can_escape_by_one_stride :
    fourthExtent.positions ⊆ parentExtent.positions ∧
    escapedExtent.base = fourthExtent.base + fourthExtent.length ∧
    escapedExtent.positions ⊆ (⟨0,10⟩ : Range).positions ∧
    ¬ escapedExtent.positions ⊆ parentExtent.positions := by
  refine ⟨?_,rfl,?_,?_⟩
  · intro n member; rw [range_membership] at member ⊢
    simp only [fourthExtent,Range.finish,parentExtent] at member ⊢; omega
  · intro n member; rw [range_membership] at member ⊢
    simp only [escapedExtent,Range.finish] at member ⊢; omega
  · intro subset
    have bad := subset (show 8 ∈ escapedExtent.positions by
      rw [range_membership]; decide)
    rw [range_membership] at bad; simp [parentExtent,Range.finish] at bad

def parentPlacement : Placement :=
  ⟨region,(Finset.range 8).image AbstractByteId.mk⟩
def physical : PhysicalState :=
  ⟨world,fun l => if l = location then some parentPlacement else none⟩

theorem physical_wf :
    PhysicalWellFormed (fun l => l ∈ state.base.liveRoots) physical := by
  constructor
  · intro r rm q qm different
    exact False.elim (different ((Finset.mem_singleton.mp rm).trans (Finset.mem_singleton.mp qm).symm))
  · intro l; by_cases same : l = location <;> simp [physical,state,same]
  · intro l pl placed
    by_cases same : l = location
    · have eq : pl = parentPlacement := by simpa [physical,same] using placed.symm
      subst pl; simp [parentPlacement,physical,world]
    · simp [physical,same] at placed
  · intro l pl placed
    by_cases same : l = location
    · have eq : pl = parentPlacement := by simpa [physical,same] using placed.symm
      subst pl
      apply Finset.image_subset_image
      intro n member
      exact Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp member) (by decide))
    · simp [physical,same] at placed
  · intro l m a b la mb different
    have le : l = location := by
      by_contra no; simp [physical,no] at la
    have me : m = location := by
      by_contra no; simp [physical,no] at mb
    exact False.elim (different (le.trans me.symm))

theorem child_distinct (i j : Fin 4) (different : i ≠ j) : child i ≠ child j := by
  intro same; apply different; apply Fin.ext
  have eq := congrArg PlaceId.index same
  simp only [child] at eq; omega

theorem child_parent (i : Fin 4) : F1.Parent layout rootPlace (child i) :=
  ⟨tree.root_tracked,child_tracked i,i.val,by simp [layout,path,child,rootPlace]⟩

def duplicateLayout : F1.StructuralLayout :=
  {layout with path := fun p => if p = child 1 then layout.path (child 0) else layout.path p}

theorem duplicate_projection_rejected : ¬ F1.TreeWellFormed duplicateLayout := by
  intro wf
  have bad := wf.paths_unique (child 0) (child_tracked 0) (child 1) (child_tracked 1)
    (by simp [duplicateLayout,child,layout,path])
  exact child_distinct 0 1 (by decide) bad

theorem misparented_token_rejected (i : Fin 4) :
    ¬ FieldAcquireRef True True state {(token i) with rootPlace := child i} domain :=
  acquire_rejects_wrong_root_place (by
    change rootPlace ≠ child i
    exact (child_not_root i).symm)

theorem child_is_not_erased_root (i : Fin 4) :
    ¬ F0.AcquireRef True True (F1.eraseToF0 state.base)
      ⟨location,(object.node (child i)).incarnation⟩ domain :=
  F1.FixedChange.erased_field_incarnation_cannot_acquire_as_root
    state_wf ⟨by simp [state],child_tracked i⟩ (child_not_root i) True True domain

def ended : F1.CurrentState := F1.FixedLifetime.endCandidate state location false

/-- Concrete semantic ending, with explicit fixture end authority/discardability.
No physical ending, source typechecking, or Domain finalization is inferred. -/
theorem concrete_end_step : F1.FixedLifetime.EndStep True False state location domain false ended := by
  refine ⟨state_wf,⟨⟨by simp [state],rfl,trivial⟩,by simp,by intro _; rfl,rfl⟩,?_,?_,?_⟩
  · intro m p live different
    exact False.elim (different (Finset.mem_singleton.mp live.1))
  · intro pkg member; simp [state] at member
  · simp

theorem ended_wf : F1.CurrentWellFormed ended :=
  F1.FixedLifetime.end_preserves_wellFormed concrete_end_step

theorem concrete_end_invalidates_all (i : Fin 4) :
    ¬ FieldAcquireRef True True ended (token i) domain :=
  parent_end_invalidates_all concrete_end_step.2.1 i

theorem one_live_root : state.base.liveRoots = {location} := rfl
theorem one_live_domain : state.base.liveDomains = {domain} := rfl
theorem exact_places : layout.places = {rootPlace,child 0,child 1,child 2,child 3} := by decide

theorem child_role (i : Fin 4) : F1.role layout (child i) = .fixedSubobject := by
  simp [F1.role,layout,child_not_root i]

theorem wrong_domain_rejected (i : Fin 4) :
    ¬ FieldAcquireRef True True state (token i) (⟨1⟩ : DomainId) :=
  acquire_rejects_wrong_domain (by change domain ≠ (⟨1⟩ : DomainId); decide)

theorem wrong_site_rejected (i : Fin 4) :
    ¬ FieldAcquireRef True True state {(token i) with location := ⟨1⟩} domain :=
  acquire_rejects_wrong_site state_wf
    (show F1.LiveNode state.base location (child i) from
      ⟨by simp [state],child_tracked i⟩)
    (by change (⟨1⟩ : RootLocationId) ≠ location; decide)

theorem copy_token_without_access_rejected (i : Fin 4) :
    ¬ FieldAcquireRef True False state (token i) domain :=
  acquire_rejects_missing_access not_false

theorem copy_token_without_stability_rejected (i : Fin 4) :
    ¬ FieldAcquireRef False True state (token i) domain :=
  acquire_rejects_missing_stability not_false

/-- Uses the accepted freshness certificate; does not issue a restart. -/
theorem restarted_rejects_all {restarted : F1.CurrentState}
    (restart : F1.FixedLifetime.FreshTreeRestart ended restarted location) (i : Fin 4) :
    ¬ FieldAcquireRef True True restarted (token i) domain :=
  F1.FixedLifetime.end_then_fresh_restart_rejects_old_field_token
    state_wf concrete_end_step.2.1 (current i) rfl restart

theorem untyped_content_still_wf (content : RootLocationId → PlaceId → Nat) :
    F1.CurrentWellFormed {state with content := content} :=
  SourceRichBoundary.current_wellFormed_does_not_interpret_installed_content state_wf content

/-- These are weak point predicates with World evidence supplied externally,
not a canonical derived child ref or permission issuer. -/
theorem world_evidence_is_insufficient_for_parent_mode :
    F1.CurrentWellFormed state ∧
    PhysicalWellFormed (fun l => l ∈ state.base.liveRoots) physical ∧
    EvidenceValid world parentEvidence ∧
    FieldAcquireRef True (EvidenceValid world unrelatedEvidence) state (token 3) domain ∧
    ¬ AccessLe unrelatedEvidence.access parentEvidence.access :=
  ⟨state_wf,physical_wf,world_bound_is_not_parent_bound.1,
    point_acquisition 3 _ world_bound_is_not_parent_bound.2.1,
    world_bound_is_not_parent_bound.2.2⟩

def forgedPhysical : PhysicalState :=
  {physical with placement := fun l => if l = (⟨1⟩ : RootLocationId) then some ⟨region,{⟨0⟩}⟩ else physical.placement l}

theorem overlapping_extra_root_rejected :
    ¬ PhysicalWellFormed (fun l => l ∈ ({location,⟨1⟩} : Finset RootLocationId)) forgedPhysical := by
  intro wf
  have dis := wf.rootsDisjoint location ⟨1⟩ parentPlacement ⟨region,{⟨0⟩}⟩
    (by simp [forgedPhysical,physical,location]) (by simp [forgedPhysical]) (by decide)
  exact (Finset.disjoint_left.mp dis)
    (show (⟨0⟩ : AbstractByteId) ∈ parentPlacement.occupied by decide) (by simp)

/-- The proposed child range is extra diagnostic data, absent from accepted
point/root predicates. This does not make its use a legal typed projection. -/
theorem root_checks_do_not_constrain_guessed_child_extent :
    F1.CurrentWellFormed state ∧
    PhysicalWellFormed (fun l => l ∈ state.base.liveRoots) physical ∧
    escapedExtent.positions.image AbstractByteId.mk ⊆ world.bytes region ∧
    ¬ escapedExtent.positions.image AbstractByteId.mk ⊆ parentPlacement.occupied := by
  refine ⟨state_wf,physical_wf,?_,?_⟩
  · intro b member
    rcases Finset.mem_image.mp member with ⟨n,position,rfl⟩
    have bounds := range_membership.mp position
    exact Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr
      (by simp only [escapedExtent,Range.finish] at bounds; omega),rfl⟩
  · intro subset
    have bad := subset (show (⟨8⟩ : AbstractByteId) ∈
      escapedExtent.positions.image AbstractByteId.mk by decide)
    simp [parentPlacement] at bad

end
end NewLang.Adjunct.Array4Boundary

