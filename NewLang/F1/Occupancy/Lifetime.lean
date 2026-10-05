import NewLang.F1.Occupancy.Conversion

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

/-- Consume exactly the supplied slot, and reclassify that same responsibility
as the destination root. All reviewed access/static premises remain in backing. -/
structure RawInitialize (g : Geometry) (sites : RootSiteLayout) (ci tc : Prop) (s : State)
    (source result : ClaimId) (t : TypeId) (e : Extent) (l : RootLocationId)
    (pkg : PackageId) (d : DomainId) (inc : IncarnationId) (vf : ValueFactId)
    (evidence : Evidence) (post : State) : Prop where
  sourceClaim : Has s.ledger source (.slot t e)
  resultFresh : result ∉ s.ledger.active
  backing : Backing.RawInitialize sites ci tc s.flat l pkg d inc vf (e.placement g) evidence post.flat
  ledger : post.ledger = consumeOne s.ledger source result (.root t l e)

structure RawTake (ce : Prop) (s : State) (source result : ClaimId)
    (t : TypeId) (e : Extent) (l : RootLocationId) (root : LiveRoot)
    (d : DomainId) (ptr : AccessPtr) (post : State) : Prop where
  sourceClaim : Has s.ledger source (.root t l e)
  resultFresh : result ∉ s.ledger.active
  backing : Backing.RawTake ce s.flat l root d ptr post.flat
  ledger : post.ledger = consumeOne s.ledger source result (.slot t e)

structure RawDestroy (ce : Prop) (s : State) (source result : ClaimId)
    (t : TypeId) (e : Extent) (l : RootLocationId) (root : LiveRoot)
    (d : DomainId) (ptr : AccessPtr) (post : State) : Prop where
  sourceClaim : Has s.ledger source (.root t l e)
  resultFresh : result ∉ s.ledger.active
  backing : Backing.RawDestroy ce s.flat l root d ptr post.flat
  ledger : post.ledger = consumeOne s.ledger source result (.slot t e)

def InitializeStep (g : Geometry) (layout : Layout) (sites : RootSiteLayout) (ci tc : Prop) (s : State)
    (source result : ClaimId) (t : TypeId) (e : Extent) (l : RootLocationId)
    (pkg : PackageId) (d : DomainId) (inc : IncarnationId) (vf : ValueFactId)
    (evidence : Evidence) (post : State) : Prop :=
  WellFormed g layout s ∧ RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post ∧
    WellFormed g layout post

def TakeStep (g : Geometry) (layout : Layout) (ce : Prop) (s : State) (source result : ClaimId)
    (t : TypeId) (e : Extent) (l : RootLocationId) (root : LiveRoot)
    (d : DomainId) (ptr : AccessPtr) (post : State) : Prop :=
  WellFormed g layout s ∧ RawTake ce s source result t e l root d ptr post ∧ WellFormed g layout post

def DestroyStep (g : Geometry) (layout : Layout) (ce : Prop) (s : State) (source result : ClaimId)
    (t : TypeId) (e : Extent) (l : RootLocationId) (root : LiveRoot)
    (d : DomainId) (ptr : AccessPtr) (post : State) : Prop :=
  WellFormed g layout s ∧ RawDestroy ce s source result t e l root d ptr post ∧ WellFormed g layout post

section Start
variable {g : Geometry} {layout : Layout} {sites : RootSiteLayout} {ci tc : Prop} {s post : State}
  {source result : ClaimId} {t : TypeId} {e : Extent} {l : RootLocationId} {pkg : PackageId}
  {d : DomainId} {inc : IncarnationId} {vf : ValueFactId} {evidence : Evidence}

theorem initialize_consumes_slot_and_preserves_exact_responsibility
    (raw : RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post) :
    source ∉ post.ledger.active ∧ Has post.ledger result (.root t l e) ∧
    post.flat.physical.placement l = some (e.placement g) := by
  rw [raw.ledger]
  exact ⟨consumeOne_consumes_source raw.sourceClaim.1 raw.resultFresh,
    consumeOne_produces_result _ _ _ _,(Backing.initialize_uses_destination_placement raw.backing).1⟩

theorem initialize_conserves_byte_responsibility
    (raw : RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post) :
    TotalFootprint g post.ledger = TotalFootprint g s.ledger := by
  rw [raw.ledger]; apply consumeOne_conserves_footprint g raw.sourceClaim.1 raw.resultFresh
  rw [raw.sourceClaim.2]; rfl

theorem initialize_preserves_backing_lifetime_and_scope
    (raw : RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post) :
    post.flat.physical.world = s.flat.physical.world ∧ post.ledger.scope = s.ledger.scope :=
  ⟨(Backing.initialize_uses_destination_placement raw.backing).2,by rw [raw.ledger]; rfl⟩

theorem initialize_requires_reviewed_write_access
    (raw : RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post) :
    (s.flat.physical.world.access e.region).write = true :=
  Backing.initialize_requires_destination_write raw.backing

theorem initialize_rejects_readonly_backing
    (readonly : (s.flat.physical.world.access e.region).write = false) :
    ¬ RawInitialize g sites ci tc s source result t e l pkg d inc vf evidence post :=
  fun raw => Backing.initialize_rejects_readonly_region readonly raw.backing

theorem initialize_step_erases_to_backing
    (step : InitializeStep g layout sites ci tc s source result t e l pkg d inc vf evidence post) :
    Backing.InitializeStep sites ci tc s.flat l pkg d inc vf (e.placement g) evidence post.flat :=
  ⟨wellFormed_erases_to_backing step.1,step.2.1.backing,wellFormed_erases_to_backing step.2.2⟩
end Start

section End
variable {g : Geometry} {layout : Layout} {ce : Prop} {s post : State}
  {source result : ClaimId} {t : TypeId} {e : Extent} {l : RootLocationId}
  {root : LiveRoot} {d : DomainId} {ptr : AccessPtr}

theorem take_consumes_root_and_returns_same_slot (raw : RawTake ce s source result t e l root d ptr post) :
    source ∉ post.ledger.active ∧ Has post.ledger result (.slot t e) ∧ post.flat.physical.placement l = none := by
  rw [raw.ledger]
  exact ⟨consumeOne_consumes_source raw.sourceClaim.1 raw.resultFresh,
    consumeOne_produces_result _ _ _ _,(Backing.take_ends_placement_not_backing raw.backing).1⟩

theorem destroy_consumes_root_and_returns_same_slot (raw : RawDestroy ce s source result t e l root d ptr post) :
    source ∉ post.ledger.active ∧ Has post.ledger result (.slot t e) ∧ post.flat.physical.placement l = none := by
  rw [raw.ledger]
  exact ⟨consumeOne_consumes_source raw.sourceClaim.1 raw.resultFresh,
    consumeOne_produces_result _ _ _ _,(Backing.destroy_ends_placement_not_backing raw.backing).1⟩

theorem take_conserves_byte_responsibility (raw : RawTake ce s source result t e l root d ptr post) :
    TotalFootprint g post.ledger = TotalFootprint g s.ledger := by
  rw [raw.ledger]; apply consumeOne_conserves_footprint g raw.sourceClaim.1 raw.resultFresh
  rw [raw.sourceClaim.2]; rfl

theorem destroy_conserves_byte_responsibility (raw : RawDestroy ce s source result t e l root d ptr post) :
    TotalFootprint g post.ledger = TotalFootprint g s.ledger := by
  rw [raw.ledger]; apply consumeOne_conserves_footprint g raw.sourceClaim.1 raw.resultFresh
  rw [raw.sourceClaim.2]; rfl

theorem take_does_not_end_backing (raw : RawTake ce s source result t e l root d ptr post) :
    post.flat.physical.world = s.flat.physical.world ∧ post.ledger.scope = s.ledger.scope :=
  ⟨(Backing.take_ends_placement_not_backing raw.backing).2,by rw [raw.ledger]; rfl⟩

theorem destroy_does_not_end_backing (raw : RawDestroy ce s source result t e l root d ptr post) :
    post.flat.physical.world = s.flat.physical.world ∧ post.ledger.scope = s.ledger.scope :=
  ⟨(Backing.destroy_ends_placement_not_backing raw.backing).2,by rw [raw.ledger]; rfl⟩

theorem take_transfers_value_without_placement (raw : RawTake ce s source result t e l root d ptr post) :
    post.flat.semantic.packages = s.flat.semantic.packages ∧
    F0.Survives post.flat.semantic root.package ∧ post.flat.physical.placement l = none :=
  Backing.take_transfers_value_without_source_placement raw.backing

theorem take_requires_reviewed_read_access (raw : RawTake ce s source result t e l root d ptr post) :
    ptr.evidence.access.read = true ∧ (s.flat.physical.world.access ptr.evidence.region).read = true :=
  Backing.take_requires_source_read raw.backing

theorem take_rejects_writeonly_ptr (writeonly : ptr.evidence.access.read = false) :
    ¬ RawTake ce s source result t e l root d ptr post := fun raw =>
  Backing.take_rejects_writeonly_ptr writeonly raw.backing

theorem take_step_erases_to_backing (step : TakeStep g layout ce s source result t e l root d ptr post) :
    Backing.TakeStep ce s.flat l root d ptr post.flat :=
  ⟨wellFormed_erases_to_backing step.1,step.2.1.backing,wellFormed_erases_to_backing step.2.2⟩

theorem destroy_step_erases_to_backing (step : DestroyStep g layout ce s source result t e l root d ptr post) :
    Backing.DestroyStep ce s.flat l root d ptr post.flat :=
  ⟨wellFormed_erases_to_backing step.1,step.2.1.backing,wellFormed_erases_to_backing step.2.2⟩

theorem take_then_same_range_restart_rejects_stale_ptr {sites : RootSiteLayout} {ci tc : Prop}
    {final : State} {newRoot : ClaimId} {pkg : PackageId} {inc : IncarnationId}
    {vf : ValueFactId} {evidence : Evidence} (wf : WellFormed g layout s)
    (taken : RawTake ce s source result t e l root d ptr post)
    (started : RawInitialize g sites ci tc post result newRoot t e l pkg d inc vf evidence final) :
    ¬ CurrentAccessPtr final.flat ptr :=
  Backing.take_then_restart_rejects_old_ptr (wellFormed_erases_to_backing wf) taken.backing started.backing

end End

/-- Only the semantic-authority frame of a representation mutation is modeled.
There is no per-byte Defined/Unspecified state or raw byte operation implementation. -/
structure RepresentationObservation where
  authority : State
  opaqueContents : Nat

def RepresentationOnlyStep (before after : RepresentationObservation) : Prop := after.authority = before.authority

theorem representation_mutation_cannot_mint_authority {before after : RepresentationObservation}
    (frame : RepresentationOnlyStep before after) :
    after.authority.ledger = before.authority.ledger ∧ after.authority.flat = before.authority.flat := by
  rw [frame]; exact ⟨rfl,rfl⟩

end
end NewLang.F1.Occupancy
