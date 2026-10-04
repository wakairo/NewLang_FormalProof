import NewLang.F0.Package
import Mathlib.Data.Set.Basic

namespace NewLang.F0

/-- Place/state-owned information; governing domain is not package-owned. -/
structure LiveRoot where
  place : PlaceId
  incarnation : IncarnationId
  currentFact : ValueFactId
  package : PackageId
  governing : DomainId
  deriving DecidableEq, Repr

/-- A location cannot simultaneously be vacant and live. -/
inductive Occupancy where
  | vacant
  | live (root : LiveRoot)
  deriving DecidableEq, Repr

/-- F0 bridge §9. These functions are abstract maps, not runtime data structures. -/
structure State where
  occupancy : RootLocationId → Occupancy
  packages : PackageId → Option ValuePackage
  loosePackages : Finset PackageId
  liveDomains : Finset DomainId
  /-- Proof-only allocation history; never shrink it when a fact stops being live. -/
  usedValueFacts : Finset ValueFactId

/-- Fresh means never allocated in the recorded history, not merely currently dead. -/
def FreshValueFact (s : State) (fact : ValueFactId) : Prop :=
  fact ∉ s.usedValueFacts

/-- Installed carriers use locations to distinguish even malformed duplicate roots. -/
inductive Carrier where
  | installed (location : RootLocationId)
  | loose
  deriving DecidableEq, Repr

def Carries (s : State) (pkg : PackageId) : Carrier → Prop
  | .installed location =>
      ∃ root, s.occupancy location = .live root ∧ root.package = pkg
  | .loose => pkg ∈ s.loosePackages

def IsInstalled (s : State) (pkg : PackageId) : Prop :=
  ∃ location, Carries s pkg (.installed location)

/-- Table entries without a carrier are not surviving values. -/
def Survives (s : State) (pkg : PackageId) : Prop :=
  IsInstalled s pkg ∨ pkg ∈ s.loosePackages

/-- Derived view, never an independently mutable source of truth (F0 bridge §5). -/
def LiveFacts (s : State) : Set Fact := fun fact =>
  match fact with
  | .valueFact place currentFact =>
      ∃ location root,
        s.occupancy location = .live root ∧
        root.place = place ∧ root.currentFact = currentFact
  | .domainLive domain => domain ∈ s.liveDomains

/-- No roots, packages or domains; unspecified locations are vacant. -/
def State.empty : State where
  occupancy := fun _ => .vacant
  packages := fun _ => none
  loosePackages := ∅
  liveDomains := ∅
  usedValueFacts := ∅

end NewLang.F0
