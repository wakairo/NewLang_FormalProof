import NewLang.F1.Backing.Model

namespace NewLang.F1.Backing
open F0
noncomputable section

/-- Lift the reviewed whole replace/store relation without moving backing. -/
structure RawWhole (w ty : Prop) (s : SumState) (l : RootLocationId)
    (incoming : PackageId) (v : Conditional.SumValue) (a : Conditional.Allocation)
    (returnsOld : Bool) (post : SumState) : Prop where
  semantic : Conditional.RawWhole w ty s.semantic l incoming v a returnsOld post.semantic
  destinationWrite : WriteAt s.physical l
  physical : post.physical = s.physical

def WholeStep (w ty : Prop) (s : SumState) (l : RootLocationId)
    (incoming : PackageId) (v : Conditional.SumValue) (a : Conditional.Allocation)
    (returnsOld : Bool) (post : SumState) : Prop :=
  SumWellFormed s ∧ RawWhole w ty s l incoming v a returnsOld post ∧ SumWellFormed post

structure RawPayload (w ty : Prop) (s : SumState) (l : RootLocationId)
    (incoming result : PackageId) (old : Conditional.SumValue) (new : Conditional.PayloadValue)
    (capability : Bool) (rootFact payloadFact : ValueFactId) (returnsOld : Bool) (post : SumState) : Prop where
  semantic : Conditional.RawPayload w ty s.semantic l incoming result old new capability
    rootFact payloadFact returnsOld post.semantic
  destinationWrite : WriteAt s.physical l
  physical : post.physical = s.physical

def PayloadStep (w ty : Prop) (s : SumState) (l : RootLocationId)
    (incoming result : PackageId) (old : Conditional.SumValue) (new : Conditional.PayloadValue)
    (capability : Bool) (rootFact payloadFact : ValueFactId) (returnsOld : Bool) (post : SumState) : Prop :=
  SumWellFormed s ∧ RawPayload w ty s l incoming result old new capability
    rootFact payloadFact returnsOld post ∧ SumWellFormed post

structure RawSwap (w ty : Prop) (s : SumState) (left right : RootLocationId) (post : SumState) : Prop where
  semantic : Conditional.RawSwap w ty s.semantic left right post.semantic
  leftWrite : WriteAt s.physical left
  rightWrite : WriteAt s.physical right
  physical : post.physical = s.physical

def SwapStep (w ty : Prop) (s : SumState) (left right : RootLocationId) (post : SumState) : Prop :=
  SumWellFormed s ∧ RawSwap w ty s left right post ∧ SumWellFormed post

theorem whole_preserves_placement {w ty : Prop} {s post : SumState} {l incoming v a returnsOld}
    (raw : RawWhole w ty s l incoming v a returnsOld post) :
    post.physical.placement = s.physical.placement ∧ post.physical.world = s.physical.world := by
  rw [raw.physical]; exact ⟨rfl, rfl⟩

theorem whole_replace_preserves_target_placement {w ty : Prop} {s post : SumState} {l incoming v a}
    (raw : RawWhole w ty s l incoming v a true post) :
    post.physical.placement l = s.physical.placement l := by rw [raw.physical]

theorem whole_store_preserves_target_placement {w ty : Prop} {s post : SumState} {l incoming v a}
    (raw : RawWhole w ty s l incoming v a false post) :
    post.physical.placement l = s.physical.placement l := by rw [raw.physical]

theorem whole_lift_is_legal {w ty : Prop} {s : SumState} {post : Conditional.State}
    {l incoming v a returnsOld} (before : SumWellFormed s)
    (step : Conditional.WholeStep w ty s.semantic l incoming v a returnsOld post)
    (write : WriteAt s.physical l) :
    WholeStep w ty s l incoming v a returnsOld ⟨post, s.physical⟩ := by
  refine ⟨before, ⟨step.2.1, write, rfl⟩, ⟨step.2.2.toInvariant, step.2.2.dependencies, ?_⟩⟩
  simpa only [(Conditional.whole_preserves_static_frame step.2.1).1] using before.backing

theorem payload_preserves_placement {w ty : Prop} {s post : SumState}
    {l incoming result old new capability rootFact payloadFact returnsOld}
    (raw : RawPayload w ty s l incoming result old new capability rootFact payloadFact returnsOld post) :
    post.physical = s.physical := raw.physical

theorem payload_backing_wellFormed {w ty : Prop} {s post : SumState}
    {l incoming result old new capability rootFact payloadFact returnsOld}
    (wf : SumWellFormed s)
    (raw : RawPayload w ty s l incoming result old new capability rootFact payloadFact returnsOld post) :
    PhysicalWellFormed (fun m => m ∈ post.semantic.liveRoots) post.physical := by
  rw [raw.physical, raw.semantic.post_eq]
  exact wf.backing

theorem swap_same_is_identity {w ty : Prop} {s post : SumState} {l}
    (raw : RawSwap w ty s l l post) : post = s := by
  have sem := Conditional.swap_same_is_identity raw.semantic
  have phy := raw.physical
  cases s; cases post; cases sem; cases phy; rfl

theorem swap_preserves_placement_and_backing {w ty : Prop} {s post : SumState} {left right}
    (raw : RawSwap w ty s left right post) :
    post.physical.placement = s.physical.placement ∧ post.physical.world = s.physical.world := by
  rw [raw.physical]; exact ⟨rfl,rfl⟩

theorem swap_lift_is_legal {w ty : Prop} {s : SumState} {post : Conditional.State} {left right}
    (before : SumWellFormed s) (step : Conditional.SwapStep w ty s.semantic left right post)
    (leftWrite : WriteAt s.physical left) (rightWrite : WriteAt s.physical right) :
    SwapStep w ty s left right ⟨post, s.physical⟩ := by
  refine ⟨before, ⟨step.2.1,leftWrite,rightWrite,rfl⟩,
    ⟨step.2.2.toInvariant,step.2.2.dependencies,?_⟩⟩
  have roots : post.liveRoots = s.semantic.liveRoots := by
    cases step.2.1 with
    | same => rfl
    | distinct raw => exact (Conditional.swap_distinct_preserves_frame raw).2.1
  simpa only [roots] using before.backing

theorem swap_distinct_exchanges_values_not_placement {w ty : Prop} {s post : SumState}
    {left right lv rv a b} (raw : RawSwap w ty s left right post)
    (distinct : Conditional.RawSwapDistinct w ty s.semantic left right lv rv a b post.semantic) :
    post.semantic.values = s.semantic.values ∧
    post.semantic.values (post.semantic.root left).package = some (.sum rv) ∧
    post.semantic.values (post.semantic.root right).package = some (.sum lv) ∧
    post.physical.placement left = s.physical.placement left ∧
    post.physical.placement right = s.physical.placement right := by
  rcases Conditional.swap_distinct_exchanges_values_without_rewriting_dependencies distinct with ⟨table,l,r⟩
  exact ⟨table,l,r,by rw [raw.physical],by rw [raw.physical]⟩

theorem whole_step_erases {w ty : Prop} {s post : SumState} {l incoming v a returnsOld}
    (step : WholeStep w ty s l incoming v a returnsOld post) :
    Conditional.WholeStep w ty s.semantic l incoming v a returnsOld post.semantic :=
  ⟨sum_wellFormed_erases_to_conditional step.1,step.2.1.semantic,
    sum_wellFormed_erases_to_conditional step.2.2⟩

theorem swap_step_erases {w ty : Prop} {s post : SumState} {left right}
    (step : SwapStep w ty s left right post) :
    Conditional.SwapStep w ty s.semantic left right post.semantic :=
  ⟨sum_wellFormed_erases_to_conditional step.1,step.2.1.semantic,
    sum_wellFormed_erases_to_conditional step.2.2⟩


theorem payload_lift_is_legal {w ty : Prop} {s : SumState} {post : Conditional.State}
    {l incoming result old new capability rootFact payloadFact returnsOld}
    (before : SumWellFormed s)
    (step : Conditional.PayloadStep w ty s.semantic l incoming result old new capability
      rootFact payloadFact returnsOld post) (write : WriteAt s.physical l) :
    PayloadStep w ty s l incoming result old new capability rootFact payloadFact returnsOld
      ⟨post,s.physical⟩ := by
  refine ⟨before,⟨step.2.1,write,rfl⟩,⟨step.2.2.toInvariant,step.2.2.dependencies,?_⟩⟩
  rw [step.2.1.post_eq]; exact before.backing

theorem payload_step_erases {w ty : Prop} {s post : SumState}
    {l incoming result old new capability rootFact payloadFact returnsOld}
    (step : PayloadStep w ty s l incoming result old new capability rootFact payloadFact returnsOld post) :
    Conditional.PayloadStep w ty s.semantic l incoming result old new capability
      rootFact payloadFact returnsOld post.semantic :=
  ⟨sum_wellFormed_erases_to_conditional step.1,step.2.1.semantic,
    sum_wellFormed_erases_to_conditional step.2.2⟩

end
end NewLang.F1.Backing
