import NewLang.F0.State

namespace NewLang.F0

/-- No package is installed twice or both installed and loose (WF-1). -/
def CarrierUnique (s : State) : Prop :=
  ∀ pkg c₁ c₂, Carries s pkg c₁ → Carries s pkg c₂ → c₁ = c₂

/-- One live root location per place, hence one current fact per live place (WF-4). -/
def PlacesUnique (s : State) : Prop :=
  ∀ l₁ l₂ r₁ r₂,
    s.occupancy l₁ = .live r₁ → s.occupancy l₂ = .live r₂ →
    r₁.place = r₂.place → l₁ = l₂

/-- An incarnation identifies one live root; allocation history is recorded separately. -/
def IncarnationsUnique (s : State) : Prop :=
  ∀ l₁ l₂ r₁ r₂,
    s.occupancy l₁ = .live r₁ → s.occupancy l₂ = .live r₂ →
    r₁.incarnation = r₂.incarnation → l₁ = l₂

/-- Every installed or loose carrier references a defined package (WF-7). -/
def PackagesPresent (s : State) : Prop :=
  ∀ pkg, Survives s pkg → ∃ value, s.packages pkg = some value

/-- Each live root's single governing domain must be live (WF-5). -/
def DomainsValid (s : State) : Prop :=
  ∀ location root, s.occupancy location = .live root → root.governing ∈ s.liveDomains

/-- Draft 17.4 §13.5a: dependencies of all surviving packages are live (WF-6). -/
def DependenciesValid (s : State) : Prop :=
  ∀ pkg value, Survives s pkg → s.packages pkg = some value →
    ∀ fact ∈ value.dependencies, fact ∈ LiveFacts s

/-- Current identities must already have been allocated in the ghost history. -/
def ValueFactsRecorded (s : State) : Prop :=
  ∀ location root, s.occupancy location = .live root → root.currentFact ∈ s.usedValueFacts

/-- All live incarnations have been allocated in the ghost history. -/
def IncarnationsRecorded (s : State) : Prop :=
  ∀ location root, s.occupancy location = .live root → root.incarnation ∈ s.usedIncarnations

/-- Exactly one carrier for every live domain, no carrier for a dead domain.
Different domain identities may share an abstract carrier; no reverse injectivity. -/
def DomainCarrierCoherent (s : State) : Prop :=
  ∀ domain, domain ∈ s.liveDomains ↔ ∃ carrier, s.domainValueCarrier domain = some carrier

/-- WF-2/3/8 are structural: occupancy is exclusive, and its package is its carrier. -/
structure WellFormed (s : State) : Prop where
  carrierUnique : CarrierUnique s
  placesUnique : PlacesUnique s
  incarnationsUnique : IncarnationsUnique s
  packagesPresent : PackagesPresent s
  domainsValid : DomainsValid s
  dependenciesValid : DependenciesValid s
  valueFactsRecorded : ValueFactsRecorded s
  incarnationsRecorded : IncarnationsRecorded s
  domainCarrierCoherent : DomainCarrierCoherent s

theorem wellFormed_live_domain_has_value_carrier {s : State} (wf : WellFormed s)
    {domain : DomainId} (live : domain ∈ s.liveDomains) :
    ∃ carrier, s.domainValueCarrier domain = some carrier :=
  (wf.domainCarrierCoherent domain).mp live

theorem wellFormed_domain_carrier_implies_live_domain {s : State} (wf : WellFormed s)
    {domain : DomainId} {carrier : DomainValueCarrierId}
    (present : s.domainValueCarrier domain = some carrier) : domain ∈ s.liveDomains :=
  (wf.domainCarrierCoherent domain).mpr ⟨carrier, present⟩

/-- Machine-checked smoke theorem; covers installed and loose packages alike. -/
theorem wellFormed_surviving_dependencies_live
    {s : State} (h : WellFormed s) {pkg : PackageId} {value : ValuePackage}
    (survives : Survives s pkg) (present : s.packages pkg = some value)
    {fact : Fact} (dependency : fact ∈ value.dependencies) : fact ∈ LiveFacts s :=
  h.dependenciesValid pkg value survives present fact dependency

/-- The invariant admits at least the empty state; no semantic premise is assumed. -/
theorem empty_wellFormed : WellFormed State.empty := by
  constructor
  · intro pkg c₁ c₂ h₁ _
    cases c₁ <;> simp [Carries, State.empty] at h₁
  · simp [PlacesUnique, State.empty]
  · simp [IncarnationsUnique, State.empty]
  · simp [PackagesPresent, Survives, IsInstalled, Carries, State.empty]
  · simp [DomainsValid, State.empty]
  · simp [DependenciesValid, Survives, IsInstalled, Carries, State.empty]
  · simp [ValueFactsRecorded, State.empty]
  · simp [IncarnationsRecorded, State.empty]
  · simp [DomainCarrierCoherent, State.empty]

end NewLang.F0
