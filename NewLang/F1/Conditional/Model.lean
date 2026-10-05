import NewLang.F1.StructuralValue

namespace NewLang.F1.Conditional
open F0
noncomputable section

/-- Nominal identities. Occurrences are place-owned ghost state, not value data. -/
structure OccurrenceId where
  index : Nat
  deriving DecidableEq, Repr
structure SumTypeId where
  index : Nat
  deriving DecidableEq, Repr
structure VariantId where
  index : Nat
  deriving DecidableEq, Repr

/-- One uniform exact-fact vocabulary, including ordinary and conditional facts. -/
inductive Fact where
  | fixed : F0.Fact → Fact
  | occurrence : OccurrenceId → Fact
  | payloadValue : OccurrenceId → ValueFactId → Fact
  deriving DecidableEq, Repr

structure SumType where
  variants : Finset VariantId
  hasPayload : VariantId → Bool
  payloadDiscardable : VariantId → Bool

def SumType.discardable (t : SumType) : Bool :=
  if ∀ v ∈ t.variants, t.hasPayload v = true → t.payloadDiscardable v = true then true else false

structure PayloadValue where
  content : Nat
  dependencies : Finset Fact

/-- No source occurrence, place, incarnation, or domain is owned by a value.
Exact occurrence references may occur in dependencies; they are never retargeted. -/
structure SumValue where
  typeId : SumTypeId
  variant : VariantId
  rootDependencies : Finset Fact
  payload : Option PayloadValue

def SumValue.dependencies (v : SumValue) : Finset Fact :=
  v.rootDependencies ∪ (v.payload.map PayloadValue.dependencies).getD ∅

def projectFacts (deps : Finset Fact) : Finset F0.Fact :=
  deps.biUnion (fun f => match f with | .fixed a => {a} | _ => ∅)

/-- Payload-only transfer has a value carrier, but never an occurrence carrier. -/
inductive SemanticValue where
  | sum : SumValue → SemanticValue
  | payload : PayloadValue → Bool → SemanticValue

def SemanticValue.dependencies : SemanticValue → Finset Fact
  | .sum v => v.dependencies
  | .payload v _ => v.dependencies

def SemanticValue.token : SemanticValue → Nat
  | .sum v => v.variant.index
  | .payload v _ => v.content

def SemanticValue.sumValue : SemanticValue → Option SumValue
  | .sum v => some v
  | .payload _ _ => none

structure SumRoot where
  place : PlaceId
  incarnation : IncarnationId
  currentFact : ValueFactId
  package : PackageId
  governing : DomainId
  typeId : SumTypeId
  occurrence : Option OccurrenceId
  payloadFact : Option ValueFactId

/-- A root-level sum slice conservatively erased to one-node fixed layouts.
Conditional payloads are not added to the fixed incarnation/layout support. -/
structure State where
  liveRoots : Finset RootLocationId
  root : RootLocationId → SumRoot
  values : PackageId → Option SemanticValue
  loosePackages : Finset PackageId
  types : SumTypeId → SumType
  liveDomains : Finset DomainId
  domainValueCarrier : DomainId → Option DomainValueCarrierId
  usedValueFacts : Finset ValueFactId
  usedIncarnations : Finset IncarnationId
  usedOccurrences : Finset OccurrenceId

def sumAt (s : State) (pkg : PackageId) : Option SumValue :=
  (s.values pkg).bind SemanticValue.sumValue

def SemanticValue.discardable (s : State) : SemanticValue → Bool
  | .sum v => (s.types v.typeId).discardable
  | .payload _ capability => capability

def Survives (s : State) (pkg : PackageId) : Prop :=
  pkg ∈ s.loosePackages ∨ ∃ l ∈ s.liveRoots, (s.root l).package = pkg

def LiveFacts (s : State) : Set Fact := fun f => match f with
  | .fixed (.valueFact p vf) => ∃ l ∈ s.liveRoots, (s.root l).place = p ∧ (s.root l).currentFact = vf
  | .fixed (.domainLive d) => d ∈ s.liveDomains
  | .occurrence o => ∃ l ∈ s.liveRoots, (s.root l).occurrence = some o
  | .payloadValue o vf => ∃ l ∈ s.liveRoots,
      (s.root l).occurrence = some o ∧ (s.root l).payloadFact = some vf

def DependenciesValid (s : State) : Prop :=
  ∀ pkg, Survives s pkg → ∀ v, s.values pkg = some v →
    ∀ f ∈ v.dependencies, f ∈ LiveFacts s

def ValueTyped (s : State) (v : SumValue) : Prop :=
  v.variant ∈ (s.types v.typeId).variants ∧
  (v.payload.isSome = (s.types v.typeId).hasPayload v.variant)

def FreshOccurrence (s : State) (o : OccurrenceId) : Prop := o ∉ s.usedOccurrences

/-- Precision-losing erasure drops conditional facts, but retains every ordinary
fact and the entire semantic carrier. No exact transition simulation is claimed. -/
def erase (s : State) : F1.CurrentState where
  base := {
    liveRoots := s.liveRoots
    root := fun l => {
      layout := ⟨{(s.root l).place}, (s.root l).place, fun _ => []⟩
      node := fun _ => ⟨(s.root l).incarnation, (s.root l).currentFact,
        projectFacts (((s.values (s.root l).package).map SemanticValue.dependencies).getD ∅)⟩
      package := (s.root l).package
      governing := (s.root l).governing
      discardable := (s.types (s.root l).typeId).discardable }
    loosePackages := s.loosePackages
    looseValues := fun pkg => (s.values pkg).map (fun v =>
      ⟨projectFacts v.dependencies, v.discardable s⟩)
    liveDomains := s.liveDomains
    domainValueCarrier := s.domainValueCarrier
    usedValueFacts := s.usedValueFacts
    usedIncarnations := s.usedIncarnations }
  content := fun l _ => ((s.values (s.root l).package).map SemanticValue.token).getD 0
  capability := fun l _ => (s.types (s.root l).typeId).discardable
  carried := fun pkg => (s.values pkg).map (fun v =>
    ⟨{[]}, fun _ => ⟨v.token, projectFacts v.dependencies⟩,
      fun _ => v.discardable s⟩)

/-- Structural frame obligations; dependency validity is not assumed here. -/
structure FrameWellFormed (s : State) : Prop where
  placesUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots, (s.root l).place = (s.root m).place → l = m
  incarnationsUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots, (s.root l).incarnation = (s.root m).incarnation → l = m
  currentFactsUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots, (s.root l).currentFact = (s.root m).currentFact → l = m
  installedUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots, (s.root l).package = (s.root m).package → l = m
  installedNotLoose : ∀ l ∈ s.liveRoots, (s.root l).package ∉ s.loosePackages
  domainsValid : ∀ l ∈ s.liveRoots, (s.root l).governing ∈ s.liveDomains
  valueFactsRecorded : ∀ l ∈ s.liveRoots, (s.root l).currentFact ∈ s.usedValueFacts
  incarnationsRecorded : ∀ l ∈ s.liveRoots, (s.root l).incarnation ∈ s.usedIncarnations
  domainCarrierCoherent : ∀ d, d ∈ s.liveDomains ↔ ∃ c, s.domainValueCarrier d = some c

structure Invariant (s : State) : Prop where
  frame : FrameWellFormed s
  present : ∀ pkg, Survives s pkg → ∃ v, s.values pkg = some v
  typed : ∀ pkg, Survives s pkg → ∀ v, sumAt s pkg = some v → ValueTyped s v
  installedType : ∀ l ∈ s.liveRoots, ∀ v, sumAt s (s.root l).package = some v → v.typeId = (s.root l).typeId
  installedSum : ∀ l ∈ s.liveRoots, ∃ v, s.values (s.root l).package = some (.sum v)
  occurrenceShape : ∀ l ∈ s.liveRoots, ∀ v, sumAt s (s.root l).package = some v →
    (s.root l).occurrence.isSome = v.payload.isSome ∧ (s.root l).payloadFact.isSome = v.payload.isSome
  occurrencesUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots, ∀ o,
    (s.root l).occurrence = some o → (s.root m).occurrence = some o → l = m
  occurrencesRecorded : ∀ l ∈ s.liveRoots, ∀ o, (s.root l).occurrence = some o → o ∈ s.usedOccurrences
  payloadFactsRecorded : ∀ l ∈ s.liveRoots, ∀ vf, (s.root l).payloadFact = some vf → vf ∈ s.usedValueFacts

structure WellFormed (s : State) : Prop extends Invariant s where
  dependencies : DependenciesValid s

theorem projectFacts_membership {deps : Finset Fact} {f : F0.Fact} :
    f ∈ projectFacts deps ↔ Fact.fixed f ∈ deps := by
  constructor
  · intro member
    rcases Finset.mem_biUnion.mp member with ⟨a,dep,inside⟩
    cases a with
    | fixed b => have same : f = b := Finset.mem_singleton.mp inside; simpa [same] using dep
    | occurrence _ => exact False.elim (Finset.notMem_empty _ inside)
    | payloadValue _ _ => exact False.elim (Finset.notMem_empty _ inside)
  · intro dep; exact Finset.mem_biUnion.mpr ⟨.fixed f,dep,by simp⟩

theorem live_ordinary_fact_erases {s : State} {f : F0.Fact}
    (live : Fact.fixed f ∈ LiveFacts s) : f ∈ F1.StructuralLiveFacts (erase s).base := by
  cases f with
  | domainLive d => exact live
  | valueFact p vf =>
    rcases live with ⟨l,lt,place,fact⟩
    exact ⟨l,lt,by simp [erase,place],fact⟩

/-- Actual F1.1 sanity proof: ordinary dependency obligations are derived from
our single richer DependenciesValid invariant, not assumed as an erased WF premise. -/
theorem wellFormed_erases_to_currentWellFormed {s : State} (wf : WellFormed s) :
    F1.CurrentWellFormed (erase s) := by
  classical
  refine ⟨?_,?_,fun _ _ => rfl⟩
  · constructor
    · intro l _; constructor
      · simp [erase]
      · rfl
      · intro p pt q qt _; exact (Finset.mem_singleton.mp pt).trans (Finset.mem_singleton.mp qt).symm
      · intro p pt nonroot; exact False.elim (nonroot (Finset.mem_singleton.mp pt))
    · intro l m p lp mp
      have le : p = (s.root l).place := Finset.mem_singleton.mp lp.2
      have me : p = (s.root m).place := Finset.mem_singleton.mp mp.2
      exact wf.frame.placesUnique l lp.1 m mp.1 (le.symm.trans me)
    · intro l p m q lp mq same
      have locations := wf.frame.incarnationsUnique l lp.1 m mq.1 same
      refine ⟨locations,?_⟩
      exact (Finset.mem_singleton.mp lp.2).trans
        (locations.symm ▸ (Finset.mem_singleton.mp mq.2).symm)
    · intro l p m q lp mq same
      have locations := wf.frame.currentFactsUnique l lp.1 m mq.1 same
      refine ⟨locations,?_⟩
      exact (Finset.mem_singleton.mp lp.2).trans
        (locations.symm ▸ (Finset.mem_singleton.mp mq.2).symm)
    · exact wf.frame.installedUnique
    · exact wf.frame.installedNotLoose
    · intro pkg loose
      rcases wf.present pkg (Or.inl loose) with ⟨v,data⟩
      exact ⟨⟨projectFacts v.dependencies,v.discardable s⟩,by simp [erase,data]⟩
    · exact wf.frame.domainsValid
    · intro l p live f dep
      rcases wf.installedSum l live.1 with ⟨v,data⟩
      have projected : f ∈ projectFacts v.dependencies := by simpa [F1.LocalDeps,erase,data,SemanticValue.dependencies] using dep
      exact live_ordinary_fact_erases (wf.dependencies _ (Or.inr ⟨l,live.1,rfl⟩) _ data _
        (projectFacts_membership.mp projected))
    · intro pkg loose flat data f dep
      rcases wf.present pkg (Or.inl loose) with ⟨v,value⟩
      have flatEq : flat = ⟨projectFacts v.dependencies,v.discardable s⟩ :=
        Option.some.inj (data.symm.trans (by simp [erase,value]))
      subst flat
      exact live_ordinary_fact_erases (wf.dependencies pkg (Or.inl loose) v value _
        (projectFacts_membership.mp dep))
    · intro l p live; exact wf.frame.valueFactsRecorded l live.1
    · intro l p live; exact wf.frame.incarnationsRecorded l live.1
    · exact wf.frame.domainCarrierCoherent
  · intro pkg loose
    rcases wf.present pkg (Or.inl loose) with ⟨v,data⟩
    refine ⟨⟨{[]},fun _ => ⟨v.token,projectFacts v.dependencies⟩,fun _ => v.discardable s⟩,?_,?_⟩
    · simp [erase,data]
    · simp [erase,data,F1.StructuredValue.summary,F1.StructuredValue.dependencies]

theorem surviving_dependencies_are_live {s : State} (wf : WellFormed s)
    {pkg : PackageId} (carrier : Survives s pkg) {v : SemanticValue} (data : s.values pkg = some v)
    {f : Fact} (dep : f ∈ v.dependencies) : f ∈ LiveFacts s :=
  wf.dependencies pkg carrier v data f dep

theorem recorded_occurrence_is_not_fresh {s : State} (wf : WellFormed s)
    {l : RootLocationId} (live : l ∈ s.liveRoots) {o : OccurrenceId}
    (active : (s.root l).occurrence = some o) : ¬ FreshOccurrence s o := by
  exact fun fresh => fresh (wf.occurrencesRecorded l live o active)

theorem erasure_retains_ordinary_package_dependencies {s : State} {pkg : PackageId}
    {v : SemanticValue} (data : s.values pkg = some v) {f : F0.Fact}
    (dep : Fact.fixed f ∈ v.dependencies) :
    ∃ flat, (erase s).base.looseValues pkg = some flat ∧ f ∈ flat.dependencies := by
  refine ⟨⟨projectFacts v.dependencies, v.discardable s⟩, ?_, ?_⟩
  · simp [erase,data]
  · exact Finset.mem_biUnion.mpr ⟨.fixed f,dep,by simp⟩

end
end NewLang.F1.Conditional
