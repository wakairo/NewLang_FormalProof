import NewLang.F1.Conditional.Model

namespace NewLang.F1.Conditional
open F0
noncomputable section

/-- Atomic root/payload fact allocation. Absence allocates neither payload fact
nor occurrence. IDs are proof parameters, not a runtime allocator requirement. -/
structure Allocation where
  current : ValueFactId
  payload : Option (ValueFactId × OccurrenceId)

def Allocation.facts (a : Allocation) : Finset ValueFactId :=
  {a.current} ∪ (a.payload.map (fun x => ({x.1} : Finset ValueFactId))).getD ∅
def Allocation.occurrences (a : Allocation) : Finset OccurrenceId :=
  (a.payload.map (fun x => ({x.2} : Finset OccurrenceId))).getD ∅

def FreshAllocation (s : State) (a : Allocation) : Prop :=
  a.current ∉ s.usedValueFacts ∧
  ∀ vf o, a.payload = some (vf,o) →
    vf ∉ s.usedValueFacts ∧ vf ≠ a.current ∧ FreshOccurrence s o

def FitsAllocation (v : SumValue) (a : Allocation) : Prop :=
  a.payload.isSome = v.payload.isSome

def installRoot (r : SumRoot) (pkg : PackageId) (a : Allocation) : SumRoot :=
  { r with
    package := pkg
    currentFact := a.current
    occurrence := a.payload.map Prod.snd
    payloadFact := a.payload.map Prod.fst }

/-- Combined whole-sum transition. The old carrier is either returned or consumed
in this candidate, before dependency legality is checked. -/
def wholeCandidate (s : State) (l : RootLocationId) (incoming : PackageId)
    (a : Allocation) (returnsOld : Bool) : State := by
  classical
  exact {s with
    root := fun m => if m = l then installRoot (s.root m) incoming a else s.root m
    loosePackages := if returnsOld then insert (s.root l).package (s.loosePackages.erase incoming)
      else s.loosePackages.erase incoming
    usedValueFacts := s.usedValueFacts ∪ a.facts
    usedOccurrences := s.usedOccurrences ∪ a.occurrences }

structure RawWhole (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (returnsOld : Bool) (post : State) : Prop where
  target_live : l ∈ s.liveRoots
  incoming_loose : incoming ∈ s.loosePackages
  incoming_value : s.values incoming = some (.sum v)
  type_agrees : v.typeId = (s.root l).typeId
  fresh : FreshAllocation s a
  shape : FitsAllocation v a
  discardable : returnsOld = false → (s.types (s.root l).typeId).discardable = true
  write_allowed : w
  types_agree : ty
  post_eq : post = wholeCandidate s l incoming a returnsOld

def WholeStep (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (returnsOld : Bool) (post : State) : Prop :=
  WellFormed s ∧ RawWhole w ty s l incoming v a returnsOld post ∧ WellFormed post
def RawWholeReplace (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (post : State) : Prop :=
  RawWhole w ty s l incoming v a true post

def RawWholeStore (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (post : State) : Prop :=
  RawWhole w ty s l incoming v a false post

def WholeReplaceStep (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (post : State) : Prop :=
  WholeStep w ty s l incoming v a true post

def WholeStoreStep (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming : PackageId) (v : SumValue) (a : Allocation) (post : State) : Prop :=
  WholeStep w ty s l incoming v a false post

/-- Payload-only change consumes an incoming loose payload; the old payload can
be returned under a currently uncarried result ID. The enclosing sum carrier stays. -/
def payloadCandidate (s : State) (l : RootLocationId) (incoming result : PackageId)
    (old : SumValue) (new : PayloadValue) (capability : Bool)
    (rootFact payloadFact : ValueFactId) (returnsOld : Bool) : State := by
  classical
  exact {s with
    root := fun m => if m = l then {s.root m with currentFact := rootFact, payloadFact := some payloadFact}
      else s.root m
    values := fun pkg => if pkg = (s.root l).package then some (.sum {old with payload := some new})
      else if returnsOld ∧ pkg = result then old.payload.map (fun p => .payload p capability)
      else s.values pkg
    loosePackages := if returnsOld then insert result (s.loosePackages.erase incoming)
      else s.loosePackages.erase incoming
    usedValueFacts := insert rootFact (insert payloadFact s.usedValueFacts) }

structure RawPayload (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming result : PackageId) (old : SumValue) (new : PayloadValue) (capability : Bool)
    (rootFact payloadFact : ValueFactId) (returnsOld : Bool) (post : State) : Prop where
  target_live : l ∈ s.liveRoots
  old_value : s.values (s.root l).package = some (.sum old)
  old_payload : old.payload.isSome = true
  active : ∃ o, (s.root l).occurrence = some o
  incoming_loose : incoming ∈ s.loosePackages
  incoming_value : s.values incoming = some (.payload new capability)
  capability_agrees : capability = (s.types old.typeId).payloadDiscardable old.variant
  result_uncarried : returnsOld = true → ¬ Survives s result
  root_fresh : rootFact ∉ s.usedValueFacts
  payload_fresh : payloadFact ∉ s.usedValueFacts
  facts_distinct : rootFact ≠ payloadFact
  discardable : returnsOld = false → capability = true
  write_allowed : w
  types_agree : ty
  post_eq : post = payloadCandidate s l incoming result old new capability rootFact payloadFact returnsOld

def PayloadStep (w ty : Prop) (s : State) (l : RootLocationId)
    (incoming result : PackageId) (old : SumValue) (new : PayloadValue) (capability : Bool)
    (rootFact payloadFact : ValueFactId) (returnsOld : Bool) (post : State) : Prop :=
  WellFormed s ∧ RawPayload w ty s l incoming result old new capability rootFact payloadFact returnsOld post ∧
  WellFormed post

/-- Two atomic allocations must be disjoint, including their optional payload
facts and occurrence IDs. Freshness in the pre-state alone is insufficient. -/
def FreshPair (s : State) (a b : Allocation) : Prop :=
  FreshAllocation s a ∧ FreshAllocation s b ∧
  Disjoint a.facts b.facts ∧ Disjoint a.occurrences b.occurrences

def swapCandidate (s : State) (left right : RootLocationId) (a b : Allocation) : State := by
  classical
  exact {s with
    root := fun l => if l = left then installRoot (s.root l) (s.root right).package a
      else if l = right then installRoot (s.root l) (s.root left).package b else s.root l
    usedValueFacts := s.usedValueFacts ∪ a.facts ∪ b.facts
    usedOccurrences := s.usedOccurrences ∪ a.occurrences ∪ b.occurrences }

structure RawSwapDistinct (w ty : Prop) (s : State) (left right : RootLocationId)
    (lv rv : SumValue) (a b : Allocation) (post : State) : Prop where
  left_live : left ∈ s.liveRoots
  right_live : right ∈ s.liveRoots
  distinct : left ≠ right
  left_value : s.values (s.root left).package = some (.sum lv)
  right_value : s.values (s.root right).package = some (.sum rv)
  same_type : (s.root left).typeId = (s.root right).typeId
  fresh : FreshPair s a b
  left_shape : FitsAllocation rv a
  right_shape : FitsAllocation lv b
  write_allowed : w
  types_agree : ty
  post_eq : post = swapCandidate s left right a b

/-- The same-place constructor has no allocation parameters whatsoever. -/
inductive RawSwap (w ty : Prop) : State → RootLocationId → RootLocationId → State → Prop where
  | same {s l} : l ∈ s.liveRoots → w → ty → RawSwap w ty s l l s
  | distinct {s left right lv rv a b post} :
      RawSwapDistinct w ty s left right lv rv a b post → RawSwap w ty s left right post

def SwapStep (w ty : Prop) (s : State) (left right : RootLocationId) (post : State) : Prop :=
  WellFormed s ∧ RawSwap w ty s left right post ∧ WellFormed post

end
end NewLang.F1.Conditional
