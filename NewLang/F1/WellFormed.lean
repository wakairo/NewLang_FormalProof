import NewLang.F1.State

namespace NewLang.F1
open F0

def LiveNode (s : State) (l : RootLocationId) (p : PlaceId) : Prop :=
  l ∈ s.liveRoots ∧ p ∈ (s.root l).layout.places

def StructuralLiveIncarnation (s : State) (inc : IncarnationId) : Prop :=
  ∃ l p, LiveNode s l p ∧ ((s.root l).node p).incarnation = inc

/-- F1-side obligations. No embedded F0 WellFormed assumption. -/
structure WellFormed (s : State) : Prop where
  trees : ∀ l ∈ s.liveRoots, TreeWellFormed (s.root l).layout
  placesUnique : ∀ l m p, LiveNode s l p → LiveNode s m p → l = m
  incarnationsUnique : ∀ l p m q, LiveNode s l p → LiveNode s m q →
    ((s.root l).node p).incarnation = ((s.root m).node q).incarnation → l = m ∧ p = q
  currentFactsUnique : ∀ l p m q, LiveNode s l p → LiveNode s m q →
    ((s.root l).node p).currentFact = ((s.root m).node q).currentFact → l = m ∧ p = q
  installedUnique : ∀ l ∈ s.liveRoots, ∀ m ∈ s.liveRoots,
    (s.root l).package = (s.root m).package → l = m
  installedNotLoose : ∀ l ∈ s.liveRoots, (s.root l).package ∉ s.loosePackages
  loosePresent : ∀ pkg ∈ s.loosePackages, ∃ value, s.looseValues pkg = some value
  domainsValid : ∀ l ∈ s.liveRoots, (s.root l).governing ∈ s.liveDomains
  localDependenciesValid : ∀ l p, LiveNode s l p →
    ∀ fact ∈ LocalDeps (s.root l) p, fact ∈ StructuralLiveFacts s
  looseDependenciesValid : ∀ pkg ∈ s.loosePackages, ∀ value, s.looseValues pkg = some value →
    ∀ fact ∈ value.dependencies, fact ∈ StructuralLiveFacts s
  valueFactsRecorded : ∀ l p, LiveNode s l p → ((s.root l).node p).currentFact ∈ s.usedValueFacts
  incarnationsRecorded : ∀ l p, LiveNode s l p → ((s.root l).node p).incarnation ∈ s.usedIncarnations
  domainCarrierCoherent : ∀ d, d ∈ s.liveDomains ↔ ∃ c, s.domainValueCarrier d = some c

theorem live_structural_node_has_current_fact {s : State} {l : RootLocationId} {p : PlaceId}
    (h : LiveNode s l p) : Fact.valueFact p ((s.root l).node p).currentFact ∈ StructuralLiveFacts s :=
  ⟨l, h.1, h.2, rfl⟩

theorem structural_current_fact_is_recorded {s : State} (wf : WellFormed s)
    {l : RootLocationId} {p : PlaceId} (h : LiveNode s l p) :
    ((s.root l).node p).currentFact ∈ s.usedValueFacts := wf.valueFactsRecorded l p h

theorem distinct_live_nodes_have_distinct_current_fact_ids {s : State} (wf : WellFormed s)
    {l m : RootLocationId} {p q : PlaceId} (a : LiveNode s l p) (b : LiveNode s m q)
    (different : (l, p) ≠ (m, q)) : ((s.root l).node p).currentFact ≠ ((s.root m).node q).currentFact := by
  intro eq; rcases wf.currentFactsUnique l p m q a b eq with ⟨rfl, rfl⟩; exact different rfl

theorem live_structural_node_has_incarnation {s : State} {l : RootLocationId} {p : PlaceId}
    (h : LiveNode s l p) : StructuralLiveIncarnation s ((s.root l).node p).incarnation :=
  ⟨l, p, h, rfl⟩

theorem structural_incarnation_is_recorded {s : State} (wf : WellFormed s)
    {l : RootLocationId} {p : PlaceId} (h : LiveNode s l p) :
    ((s.root l).node p).incarnation ∈ s.usedIncarnations := wf.incarnationsRecorded l p h

theorem distinct_live_nodes_have_distinct_incarnations {s : State} (wf : WellFormed s)
    {l m : RootLocationId} {p q : PlaceId} (a : LiveNode s l p) (b : LiveNode s m q)
    (different : (l, p) ≠ (m, q)) : ((s.root l).node p).incarnation ≠ ((s.root m).node q).incarnation := by
  intro eq; rcases wf.incarnationsUnique l p m q a b eq with ⟨rfl, rfl⟩; exact different rfl

theorem subtree_dependencies_live {s : State} (wf : WellFormed s)
    {l : RootLocationId} (live : l ∈ s.liveRoots) {p : PlaceId} {f : Fact}
    (dep : f ∈ SubtreeDeps (s.root l) p) : f ∈ StructuralLiveFacts s := by
  classical
  rcases Finset.mem_biUnion.mp dep with ⟨q, tracked, owned⟩
  exact wf.localDependenciesValid l q ⟨live, (Finset.mem_filter.mp tracked).1⟩ f owned

end NewLang.F1
