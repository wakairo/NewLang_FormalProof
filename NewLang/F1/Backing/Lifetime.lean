import NewLang.F1.Backing.Model

namespace NewLang.F1.Backing
open F0
noncomputable section

def startPlacement (p : PhysicalState) (l : RootLocationId) (destination : Placement) : PhysicalState :=
  {p with placement := fun m => if m = l then some destination else p.placement m}

def endPlacement (p : PhysicalState) (l : RootLocationId) : PhysicalState :=
  {p with placement := fun m => if m = l then none else p.placement m}

/-- Caller responsibilities include typed empty destination, alignment and valid
representation. The destination evidence supplies ordinary write authority;
no authority or placement is recovered from the incoming semantic value. -/
structure RawInitialize (sites : RootSiteLayout) (ci tc : Prop) (s : FlatState)
    (l : RootLocationId) (pkg : PackageId) (d : DomainId) (inc : IncarnationId) (vf : ValueFactId)
    (destination : Placement) (e : Evidence) (post : FlatState) : Prop where
  semantic : F0.RawInitialize sites ci tc s.semantic l pkg d inc vf post.semantic
  evidence : EvidenceValid s.physical.world e
  region : destination.region = e.region
  write : e.access.write = true
  extent : destination.occupied ⊆ s.physical.world.bytes destination.region
  separate : ∀ m pl, s.physical.placement m = some pl → Disjoint destination.occupied pl.occupied
  physical : post.physical = startPlacement s.physical l destination

def InitializeStep (sites : RootSiteLayout) (ci tc : Prop) (s : FlatState)
    (l : RootLocationId) (pkg : PackageId) (d : DomainId) (inc : IncarnationId) (vf : ValueFactId)
    (destination : Placement) (e : Evidence) (post : FlatState) : Prop :=
  FlatWellFormed s ∧ RawInitialize sites ci tc s l pkg d inc vf destination e post ∧ FlatWellFormed post

/-- Exactly the supplied access evidence is issued, never stronger evidence. -/
def initializePtr (l : RootLocationId) (inc : IncarnationId) (e : Evidence) : AccessPtr :=
  ⟨ptrFromInitialize l inc,e⟩

structure RawTake (ce : Prop) (s : FlatState) (l : RootLocationId)
    (root : LiveRoot) (d : DomainId) (ptr : AccessPtr) (post : FlatState) : Prop where
  semantic : F0.RawTake ce s.semantic l root d post.semantic
  token : ptr.token = ⟨l,root.incarnation⟩
  current : CurrentAccessPtr s ptr
  read : ptr.evidence.access.read = true
  physical : post.physical = endPlacement s.physical l

/-- Ordinary destroy does not materialize T. Platform-specific end contracts
remain in ce; no read requirement is inherited from take. -/
structure RawDestroy (ce : Prop) (s : FlatState) (l : RootLocationId)
    (root : LiveRoot) (d : DomainId) (ptr : AccessPtr) (post : FlatState) : Prop where
  semantic : F0.RawDestroy ce s.semantic l root d post.semantic
  token : ptr.token = ⟨l,root.incarnation⟩
  current : CurrentAccessPtr s ptr
  physical : post.physical = endPlacement s.physical l

def TakeStep (ce : Prop) (s : FlatState) (l : RootLocationId)
    (root : LiveRoot) (d : DomainId) (ptr : AccessPtr) (post : FlatState) : Prop :=
  FlatWellFormed s ∧ RawTake ce s l root d ptr post ∧ FlatWellFormed post

def DestroyStep (ce : Prop) (s : FlatState) (l : RootLocationId)
    (root : LiveRoot) (d : DomainId) (ptr : AccessPtr) (post : FlatState) : Prop :=
  FlatWellFormed s ∧ RawDestroy ce s l root d ptr post ∧ FlatWellFormed post

section Start
variable {sites : RootSiteLayout} {ci tc : Prop} {s post : FlatState}
  {l : RootLocationId} {pkg : PackageId} {d : DomainId} {inc : IncarnationId} {vf : ValueFactId}
  {destination : Placement} {e : Evidence}

theorem initialize_requires_destination_write
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post) :
    (s.physical.world.access destination.region).write = true := by
  rw [raw.region]; exact evidence_cannot_amplify_write raw.evidence raw.write

theorem initialize_rejects_readonly_region
    (readonly : (s.physical.world.access destination.region).write = false) :
    ¬ RawInitialize sites ci tc s l pkg d inc vf destination e post := by
  intro raw; have write := initialize_requires_destination_write raw
  rw [readonly] at write; cases write

theorem initialize_rejects_readonly_evidence (readonly : e.access.write = false) :
    ¬ RawInitialize sites ci tc s l pkg d inc vf destination e post := by
  intro raw; have write := raw.write; rw [readonly] at write; cases write

theorem initialize_uses_destination_placement
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post) :
    post.physical.placement l = some destination ∧ post.physical.world = s.physical.world := by
  rw [raw.physical]; exact ⟨by simp [startPlacement],rfl⟩

theorem initialize_preserves_other_placements
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post)
    {m : RootLocationId} (other : m ≠ l) : post.physical.placement m = s.physical.placement m := by
  rw [raw.physical]; simp [startPlacement,other]

theorem initialize_produces_current_ptr
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post) :
    CurrentAccessPtr post (initializePtr l inc e) := by
  refine ⟨⟨_,raw.semantic.target_after,rfl⟩,?_,destination,?_,raw.region⟩
  · rw [(initialize_uses_destination_placement raw).2]; exact raw.evidence
  · exact (initialize_uses_destination_placement raw).1

theorem initialize_ptr_access_nonamplification
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post) :
    AccessLe (initializePtr l inc e).evidence.access (post.physical.world.access destination.region) := by
  rw [(initialize_uses_destination_placement raw).2,raw.region]; exact raw.evidence.2

/-- Semantic table transport has no source-placement field to transfer. -/
theorem initialize_value_transfer_does_not_transfer_placement
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post)
    {value : ValuePackage} (data : s.semantic.packages pkg = some value) :
    post.semantic.packages pkg = some value ∧ post.physical.placement l = some destination := by
  exact ⟨by rw [F0.initialize_preserves_package_data raw.semantic]; exact data,
    (initialize_uses_destination_placement raw).1⟩

theorem initialize_reused_placement_does_not_revive_old_ptr
    (raw : RawInitialize sites ci tc s l pkg d inc vf destination e post)
    {old : AccessPtr} (location : old.token.location = l)
    (used : old.token.incarnation ∈ s.semantic.usedIncarnations) : ¬ CurrentAccessPtr post old := by
  rintro ⟨⟨root,live,sameInc⟩,_,_⟩
  rw [location,raw.semantic.target_after] at live
  cases live
  change inc = old.token.incarnation at sameInc
  exact raw.semantic.fresh_incarnation (sameInc.symm ▸ used)

end Start

section End
variable {ce : Prop} {s post : FlatState} {l : RootLocationId}
  {root : LiveRoot} {d : DomainId} {ptr : AccessPtr}

theorem take_requires_source_read (raw : RawTake ce s l root d ptr post) :
    ptr.evidence.access.read = true ∧ (s.physical.world.access ptr.evidence.region).read = true :=
  ⟨raw.read,evidence_cannot_amplify_read raw.current.2.1 raw.read⟩

theorem take_rejects_writeonly_ptr (writeonly : ptr.evidence.access.read = false) :
    ¬ RawTake ce s l root d ptr post := by
  intro raw; have read := raw.read; rw [writeonly] at read; cases read

theorem take_rejects_writeonly_region
    (writeonly : (s.physical.world.access ptr.evidence.region).read = false) :
    ¬ RawTake ce s l root d ptr post := by
  intro raw; have read := (take_requires_source_read raw).2; rw [writeonly] at read; cases read

theorem take_ends_placement_not_backing (raw : RawTake ce s l root d ptr post) :
    post.physical.placement l = none ∧ post.physical.world = s.physical.world := by
  rw [raw.physical]; exact ⟨by simp [endPlacement],rfl⟩

theorem destroy_ends_placement_not_backing (raw : RawDestroy ce s l root d ptr post) :
    post.physical.placement l = none ∧ post.physical.world = s.physical.world := by
  rw [raw.physical]; exact ⟨by simp [endPlacement],rfl⟩

theorem take_live_region_remains_live (raw : RawTake ce s l root d ptr post) :
    ptr.evidence.region ∈ post.physical.world.liveRegions := by
  rw [(take_ends_placement_not_backing raw).2]; exact raw.current.2.1.1

theorem destroy_live_region_remains_live (raw : RawDestroy ce s l root d ptr post) :
    ptr.evidence.region ∈ post.physical.world.liveRegions := by
  rw [(destroy_ends_placement_not_backing raw).2]; exact raw.current.2.1.1

theorem take_transfers_value_without_source_placement (raw : RawTake ce s l root d ptr post) :
    post.semantic.packages = s.semantic.packages ∧
    F0.Survives post.semantic root.package ∧ post.physical.placement l = none :=
  ⟨F0.take_preserves_package_data raw.semantic,
    (F0.take_old_package_survives_as_loose raw.semantic).2,
    (take_ends_placement_not_backing raw).1⟩

theorem destroy_requires_discardable (raw : RawDestroy ce s l root d ptr post) :
    ∃ value, s.semantic.packages root.package = some value ∧ value.discardable = true :=
  raw.semantic.old_discardable

theorem take_then_restart_rejects_old_ptr {sites : RootSiteLayout} {ci tc : Prop}
    {final : FlatState} {pkg : PackageId} {inc : IncarnationId} {vf : ValueFactId}
    {destination : Placement} {e : Evidence} (wf : FlatWellFormed s)
    (taken : RawTake ce s l root d ptr post)
    (started : RawInitialize sites ci tc post l pkg d inc vf destination e final) :
    ¬ CurrentAccessPtr final ptr := by
  apply initialize_reused_placement_does_not_revive_old_ptr started
  · rw [taken.token]
  · have recorded := F0.take_ended_identities_remain_recorded
      (flat_wellFormed_erases_to_f0 wf) taken.semantic
    simpa only [taken.token] using recorded.1

theorem destroy_then_restart_rejects_old_ptr {sites : RootSiteLayout} {ci tc : Prop}
    {final : FlatState} {pkg : PackageId} {inc : IncarnationId} {vf : ValueFactId}
    {destination : Placement} {e : Evidence} (wf : FlatWellFormed s)
    (ended : RawDestroy ce s l root d ptr post)
    (started : RawInitialize sites ci tc post l pkg d inc vf destination e final) :
    ¬ CurrentAccessPtr final ptr := by
  apply initialize_reused_placement_does_not_revive_old_ptr started
  · rw [ended.token]
  · have recorded := F0.destroy_ended_identities_remain_recorded
      (flat_wellFormed_erases_to_f0 wf) ended.semantic
    simpa only [ended.token] using recorded.1

end End

/-- These erase only physical/access precision, retaining every F0 obligation. -/
theorem initialize_step_erases {sites : RootSiteLayout} {ci tc : Prop} {s post : FlatState}
    {l pkg d inc vf destination e}
    (step : InitializeStep sites ci tc s l pkg d inc vf destination e post) :
    F0.InitializeStep sites ci tc s.semantic l pkg d inc vf post.semantic :=
  ⟨flat_wellFormed_erases_to_f0 step.1,step.2.1.semantic,flat_wellFormed_erases_to_f0 step.2.2⟩

theorem take_step_erases {ce : Prop} {s post : FlatState} {l root d ptr}
    (step : TakeStep ce s l root d ptr post) :
    F0.TakeStep ce s.semantic l root d post.semantic :=
  ⟨flat_wellFormed_erases_to_f0 step.1,step.2.1.semantic,flat_wellFormed_erases_to_f0 step.2.2⟩

theorem destroy_step_erases {ce : Prop} {s post : FlatState} {l root d ptr}
    (step : DestroyStep ce s l root d ptr post) :
    F0.DestroyStep ce s.semantic l root d post.semantic :=
  ⟨flat_wellFormed_erases_to_f0 step.1,step.2.1.semantic,flat_wellFormed_erases_to_f0 step.2.2⟩

end
end NewLang.F1.Backing
