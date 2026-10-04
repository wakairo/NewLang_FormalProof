import NewLang.F1.WellFormed

namespace NewLang.F1
open F0
noncomputable section

/-- Derived from the single canonical root node; no stored flat root copy. -/
def eraseRoot (r : StructuredRoot) : F0.LiveRoot :=
  ⟨r.layout.root, (r.node r.layout.root).incarnation, (r.node r.layout.root).currentFact,
    r.package, r.governing⟩

/-- Strategy A: exact live structural value facts widen to their enclosing root.
Non-live/unknown value facts are retained; domain facts retain their identity. -/
def eraseFact (s : State) : Fact → Fact := by
  classical
  exact fun fact => match fact with
    | .domainLive d => .domainLive d
    | .valueFact p vf =>
      if h : ∃ l ∈ s.liveRoots, p ∈ (s.root l).layout.places ∧ ((s.root l).node p).currentFact = vf then
        let r := s.root (Classical.choose h)
        .valueFact r.layout.root (r.node r.layout.root).currentFact
      else .valueFact p vf

def installedOwners (s : State) (pkg : PackageId) : Finset RootLocationId :=
  s.liveRoots.filter (fun l => (s.root l).package = pkg)

def erasedDependencies (s : State) (pkg : PackageId) : Finset Fact :=
  (installedOwners s pkg).biUnion (fun l => (SubtreeDeps (s.root l) (s.root l).layout.root).image (eraseFact s))

def eraseLooseValue (s : State) (value : ValuePackage) : ValuePackage :=
  ⟨value.dependencies.image (eraseFact s), value.discardable⟩

/-- Installed package data is derived. The finite union is unambiguous under
installedUnique; loose table entries remain data even without a carrier. -/
def erasePackages (s : State) (pkg : PackageId) : Option ValuePackage :=
  if (installedOwners s pkg).Nonempty then
    some ⟨erasedDependencies s pkg,
      (installedOwners s pkg).toList.all (fun l => (s.root l).discardable)⟩
  else (s.looseValues pkg).map (eraseLooseValue s)

def eraseToF0 (s : State) : F0.State where
  occupancy := fun l => if l ∈ s.liveRoots then .live (eraseRoot (s.root l)) else .vacant
  packages := erasePackages s
  loosePackages := s.loosePackages
  liveDomains := s.liveDomains
  domainValueCarrier := s.domainValueCarrier
  usedValueFacts := s.usedValueFacts
  usedIncarnations := s.usedIncarnations

theorem erase_occupancy_live_iff (s : State) (l : RootLocationId) (r : F0.LiveRoot) :
    (eraseToF0 s).occupancy l = .live r ↔ l ∈ s.liveRoots ∧ eraseRoot (s.root l) = r := by
  by_cases live : l ∈ s.liveRoots <;> simp [eraseToF0, live]

theorem erase_root_fact_matches_f0 {s : State} {l : RootLocationId} (h : l ∈ s.liveRoots) :
    ∃ r, (eraseToF0 s).occupancy l = .live r ∧ r.currentFact = ((s.root l).node (s.root l).layout.root).currentFact :=
  ⟨eraseRoot (s.root l), (erase_occupancy_live_iff _ _ _).mpr ⟨h, rfl⟩, rfl⟩

theorem erase_root_incarnation_matches_f0 {s : State} {l : RootLocationId} (h : l ∈ s.liveRoots) :
    ∃ r, (eraseToF0 s).occupancy l = .live r ∧ r.incarnation = ((s.root l).node (s.root l).layout.root).incarnation :=
  ⟨eraseRoot (s.root l), (erase_occupancy_live_iff _ _ _).mpr ⟨h, rfl⟩, rfl⟩

theorem erase_preserves_root_governing_domain {s : State} {l : RootLocationId} (h : l ∈ s.liveRoots) :
    ∃ r, (eraseToF0 s).occupancy l = .live r ∧ r.governing = (s.root l).governing :=
  ⟨eraseRoot (s.root l), (erase_occupancy_live_iff _ _ _).mpr ⟨h, rfl⟩, rfl⟩

theorem erase_preserves_live_domains (s : State) : (eraseToF0 s).liveDomains = s.liveDomains := rfl

theorem erase_preserves_domain_carriers (s : State) : (eraseToF0 s).domainValueCarrier = s.domainValueCarrier := rfl

theorem erase_preserves_histories (s : State) :
    (eraseToF0 s).usedValueFacts = s.usedValueFacts ∧ (eraseToF0 s).usedIncarnations = s.usedIncarnations := ⟨rfl, rfl⟩

theorem erase_live_fact {s : State} {fact : Fact} (h : fact ∈ StructuralLiveFacts s) :
    eraseFact s fact ∈ F0.LiveFacts (eraseToF0 s) := by
  classical
  cases fact with
  | domainLive d => exact h
  | valueFact p vf =>
    change (∃ l ∈ s.liveRoots, p ∈ (s.root l).layout.places ∧ ((s.root l).node p).currentFact = vf) at h
    simp only [eraseFact, dite_eq_left h]
    have live := (Classical.choose_spec h).1
    exact ⟨Classical.choose h, eraseRoot (s.root (Classical.choose h)),
      (erase_occupancy_live_iff _ _ _).mpr ⟨live, rfl⟩, rfl, rfl⟩

theorem erase_structural_value_fact_to_root {s : State} (wf : WellFormed s)
    {l : RootLocationId} {p : PlaceId} (live : LiveNode s l p) :
    eraseFact s (.valueFact p ((s.root l).node p).currentFact) =
      .valueFact (s.root l).layout.root ((s.root l).node (s.root l).layout.root).currentFact := by
  have found : ∃ m ∈ s.liveRoots, p ∈ (s.root m).layout.places ∧
      ((s.root m).node p).currentFact = ((s.root l).node p).currentFact := ⟨l, live.1, live.2, rfl⟩
  simp only [eraseFact, dite_eq_left found]
  have picked := Classical.choose_spec found
  have same := wf.placesUnique (Classical.choose found) l p ⟨picked.1, picked.2.1⟩ live
  rw [same]

theorem erase_dependencies_are_conservative {s : State} {l : RootLocationId} (h : l ∈ s.liveRoots)
    {fact : Fact} (dep : fact ∈ SubtreeDeps (s.root l) (s.root l).layout.root) :
    eraseFact s fact ∈ erasedDependencies s (s.root l).package := by
  classical
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_filter.mpr ⟨h, rfl⟩, Finset.mem_image.mpr ⟨fact, dep, rfl⟩⟩

theorem erase_installed_package_present {s : State} {l : RootLocationId} (h : l ∈ s.liveRoots) :
    ∃ value, (eraseToF0 s).packages (s.root l).package = some value ∧
      value.dependencies = erasedDependencies s (s.root l).package := by
  have nonempty : (installedOwners s (s.root l).package).Nonempty :=
    ⟨l, Finset.mem_filter.mpr ⟨h, rfl⟩⟩
  simp [eraseToF0, erasePackages, nonempty]

theorem installed_owner_is_unique {s : State} (wf : WellFormed s) {l : RootLocationId}
    (live : l ∈ s.liveRoots) : installedOwners s (s.root l).package = {l} := by
  ext m
  simp only [installedOwners, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨mt, same⟩; exact wf.installedUnique m mt l live same
  · rintro rfl; exact ⟨live, rfl⟩

theorem erase_root_package_exact {s : State} (wf : WellFormed s) {l : RootLocationId}
    (live : l ∈ s.liveRoots) : (eraseToF0 s).packages (s.root l).package =
      some ⟨(SubtreeDeps (s.root l) (s.root l).layout.root).image (eraseFact s), (s.root l).discardable⟩ := by
  simp [eraseToF0, erasePackages, erasedDependencies, installed_owner_is_unique wf live]

theorem erase_local_dependency_obligation {s : State} (wf : WellFormed s)
    {l : RootLocationId} {p : PlaceId} (live : LiveNode s l p) {fact : Fact}
    (dep : fact ∈ LocalDeps (s.root l) p) :
    ∃ value, (eraseToF0 s).packages (s.root l).package = some value ∧ eraseFact s fact ∈ value.dependencies := by
  have rootDep := ancestor_subtree_deps_subset
    (root_contains_every_place (wf.trees l live.1) live.2)
    (local_deps_subset_subtree_deps live.2 dep)
  obtain ⟨value, present, deps⟩ := erase_installed_package_present live.1
  exact ⟨value, present, by rw [deps]; exact erase_dependencies_are_conservative live.1 rootDep⟩

/-- Each F0 invariant is derived separately from F1-side structure/ownership. -/
theorem erase_carrier_unique {s : State} (wf : WellFormed s) : F0.CarrierUnique (eraseToF0 s) := by
  intro pkg a b ha hb
  cases a <;> cases b
  · rcases ha with ⟨ra, liveA, packageA⟩; rcases hb with ⟨rb, liveB, packageB⟩
    rcases (erase_occupancy_live_iff _ _ _).mp liveA with ⟨ltA, rfl⟩
    rcases (erase_occupancy_live_iff _ _ _).mp liveB with ⟨ltB, rfl⟩
    congr 1; exact wf.installedUnique _ ltA _ ltB (packageA.trans packageB.symm)
  · rcases ha with ⟨r, live, package⟩
    rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
    exact False.elim (wf.installedNotLoose _ lt (by change (s.root _).package = pkg at package; exact package.symm ▸ hb))
  · rcases hb with ⟨r, live, package⟩
    rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
    exact False.elim (wf.installedNotLoose _ lt (by change (s.root _).package = pkg at package; exact package.symm ▸ ha))
  · rfl

theorem erase_places_unique {s : State} (wf : WellFormed s) : F0.PlacesUnique (eraseToF0 s) := by
  intro l m a b ha hb same
  rcases (erase_occupancy_live_iff _ _ _).mp ha with ⟨lt, rfl⟩
  rcases (erase_occupancy_live_iff _ _ _).mp hb with ⟨mt, rfl⟩
  exact wf.placesUnique l m (s.root l).layout.root ⟨lt, (wf.trees l lt).root_tracked⟩
    ⟨mt, by change (s.root l).layout.root = (s.root m).layout.root at same; rw [same]; exact (wf.trees m mt).root_tracked⟩

theorem erase_incarnations_unique {s : State} (wf : WellFormed s) : F0.IncarnationsUnique (eraseToF0 s) := by
  intro l m a b ha hb same
  rcases (erase_occupancy_live_iff _ _ _).mp ha with ⟨lt, rfl⟩
  rcases (erase_occupancy_live_iff _ _ _).mp hb with ⟨mt, rfl⟩
  exact (wf.incarnationsUnique l _ m _ ⟨lt, (wf.trees l lt).root_tracked⟩
    ⟨mt, (wf.trees m mt).root_tracked⟩ same).1

theorem erase_packages_present {s : State} (wf : WellFormed s) : F0.PackagesPresent (eraseToF0 s) := by
  classical
  intro pkg surviving
  rcases surviving with ⟨l, r, live, package⟩ | loose
  · rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
    obtain ⟨v, present, _⟩ := erase_installed_package_present lt
    exact ⟨v, package ▸ present⟩
  · have none : ¬ (installedOwners s pkg).Nonempty := by
      rintro ⟨l, owner⟩; rcases Finset.mem_filter.mp owner with ⟨lt, eq⟩
      exact wf.installedNotLoose l lt (eq ▸ loose)
    obtain ⟨v, present⟩ := wf.loosePresent pkg loose
    exact ⟨eraseLooseValue s v, by simp [eraseToF0, erasePackages, none, present]⟩

theorem erase_domains_valid {s : State} (wf : WellFormed s) : F0.DomainsValid (eraseToF0 s) := by
  intro l r live
  rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
  exact wf.domainsValid l lt

theorem erase_dependencies_valid {s : State} (wf : WellFormed s) : F0.DependenciesValid (eraseToF0 s) := by
  classical
  intro pkg value surviving present fact dep
  by_cases installed : (installedOwners s pkg).Nonempty
  · have same := Option.some.inj (show some _ = some value from (by simpa [eraseToF0, erasePackages, installed] using present))
    have deps : fact ∈ erasedDependencies s pkg := by simpa [← same] using dep
    rcases Finset.mem_biUnion.mp deps with ⟨l, owner, image⟩
    rcases Finset.mem_filter.mp owner with ⟨lt, _⟩
    rcases Finset.mem_image.mp image with ⟨source, sourceDep, rfl⟩
    exact erase_live_fact (subtree_dependencies_live wf lt sourceDep)
  · have loose : pkg ∈ s.loosePackages := by
      rcases surviving with ⟨l, r, live, package⟩ | loose
      · rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
        exact False.elim (installed ⟨l, Finset.mem_filter.mpr ⟨lt, package⟩⟩)
      · exact loose
    obtain ⟨v, data⟩ := wf.loosePresent pkg loose
    have same : eraseLooseValue s v = value := Option.some.inj (by simpa [eraseToF0, erasePackages, installed, data] using present)
    have image : fact ∈ v.dependencies.image (eraseFact s) := by simpa [← same, eraseLooseValue] using dep
    rcases Finset.mem_image.mp image with ⟨source, sourceDep, rfl⟩
    exact erase_live_fact (wf.looseDependenciesValid pkg loose v data source sourceDep)

theorem erase_value_facts_recorded {s : State} (wf : WellFormed s) : F0.ValueFactsRecorded (eraseToF0 s) := by
  intro l r live
  rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
  exact wf.valueFactsRecorded l _ ⟨lt, (wf.trees l lt).root_tracked⟩

theorem erase_incarnations_recorded {s : State} (wf : WellFormed s) : F0.IncarnationsRecorded (eraseToF0 s) := by
  intro l r live
  rcases (erase_occupancy_live_iff _ _ _).mp live with ⟨lt, rfl⟩
  exact wf.incarnationsRecorded l _ ⟨lt, (wf.trees l lt).root_tracked⟩

theorem erase_domain_carrier_coherent {s : State} (wf : WellFormed s) : F0.DomainCarrierCoherent (eraseToF0 s) :=
  wf.domainCarrierCoherent

theorem f1_wellFormed_erases_to_f0_wellFormed {s : State} (wf : WellFormed s) : F0.WellFormed (eraseToF0 s) :=
  ⟨erase_carrier_unique wf, erase_places_unique wf, erase_incarnations_unique wf,
   erase_packages_present wf, erase_domains_valid wf, erase_dependencies_valid wf,
   erase_value_facts_recorded wf, erase_incarnations_recorded wf, erase_domain_carrier_coherent wf⟩

end
end NewLang.F1
