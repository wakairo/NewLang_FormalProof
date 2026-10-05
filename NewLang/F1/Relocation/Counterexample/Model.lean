import NewLang.F1.Relocation.Accounting
import NewLang.F1.Occupancy.Counterexample.Fixtures

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing
open Occupancy.Counterexample (geometry layout ty cid region rw ro wo)
noncomputable section

inductive Case where | overlap | disjoint | different | equal
  deriving DecidableEq

def sites : RootSiteLayout := ⟨fun l => ⟨l.index⟩,by
  intro a b eq; exact congrArg (fun p : PlaceId => RootLocationId.mk p.index) eq⟩
def source : RootLocationId := ⟨0⟩
def destination : RootLocationId := ⟨1⟩
def pkg : PackageId := ⟨0⟩
def external : PackageId := ⟨1⟩
def srcExtent : Occupancy.Extent := ⟨region 0,⟨0,2⟩⟩
def dstExtent : Case → Occupancy.Extent
  | .overlap => ⟨region 0,⟨1,2⟩⟩
  | .disjoint => ⟨region 0,⟨2,2⟩⟩
  | .different => ⟨region 1,⟨0,2⟩⟩
  | .equal => srcExtent

def inputExtent : Case → Occupancy.Extent
  | .overlap => ⟨region 0,⟨2,1⟩⟩
  | k => dstExtent k

def outputExtent : Case → Occupancy.Extent
  | .overlap => ⟨region 0,⟨0,1⟩⟩
  | _ => srcExtent

def frameExtent : Case → Occupancy.Extent
  | .overlap => ⟨region 0,⟨3,1⟩⟩
  | _ => ⟨region 0,⟨2,2⟩⟩

def regions : Case → Finset BackingRegionId
  | .different => {region 0,region 1}
  | _ => {region 0}

def world (k : Case) (a : Access) : World :=
  ⟨regions k,fun r => (Finset.range 4).image (geometry.byteAt r),fun _ => a⟩
def inputIds (k : Case) : Finset Occupancy.ClaimId := if k = .equal then ∅ else {cid 1}
def frameIds : Case → Finset Occupancy.ClaimId
  | .overlap | .equal => {cid 2}
  | .disjoint => ∅
  | .different => {cid 2,cid 5}

def beforeLedger (k : Case) : Occupancy.Ledger :=
  ⟨regions k,insert (cid 0) (inputIds k ∪ frameIds k),fun id =>
    if id = cid 0 then .root ty source srcExtent
    else if id = cid 1 then .storage (inputExtent k)
    else if id = cid 5 then .storage ⟨region 1,⟨2,2⟩⟩ else .storage (frameExtent k)⟩

def sumValue (deps : Finset Conditional.Fact) : Conditional.SumValue :=
  ⟨⟨0⟩,⟨0⟩,∅,some ⟨41,deps⟩⟩
def externalValue (deps : Finset Conditional.Fact) : Conditional.SemanticValue := .payload ⟨99,deps⟩ true

def root (l : RootLocationId) (n : Nat) : Conditional.SumRoot :=
  ⟨sites.placeAt l,⟨n⟩,⟨2*n⟩,pkg,⟨0⟩,⟨0⟩,some ⟨n⟩,some ⟨2*n+1⟩⟩
def semantic (deps ext : Finset Conditional.Fact) : Conditional.State where
  liveRoots := {source}
  root := fun _ => root source 0
  values := fun p => if p = pkg then some (.sum (sumValue deps)) else some (externalValue ext)
  loosePackages := {external}
  types := fun _ => ⟨{⟨0⟩},fun _ => true,fun _ => false⟩
  liveDomains := {⟨0⟩}
  domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
  usedValueFacts := {⟨0⟩,⟨1⟩}
  usedIncarnations := {⟨0⟩}
  usedOccurrences := {⟨0⟩,⟨9⟩}

def annotation (k : Case) (p : PackageId) : PackageData :=
  if p = pkg then ⟨[⟨source,⟨0⟩⟩],if k = .disjoint then ∅ else {cid 2},7⟩ else ⟨[],∅,0⟩
def before (k : Case) (a : Access) (deps ext : Finset Conditional.Fact) : State :=
  ⟨⟨⟨semantic deps ext,⟨world k a,fun l => if l = source then some (srcExtent.placement geometry) else none⟩⟩,
    beforeLedger k⟩,annotation k⟩

def move (k : Case) : Move where
  source := source
  destination := destination
  sourceClaim := cid 0
  newRootClaim := cid 4
  type := ty
  sourceExtent := srcExtent
  destinationExtent := dstExtent k
  inputRaw := inputIds k
  outputRaw := if k = .equal then ∅ else {cid 3}
  rawExtent := fun _ => outputExtent k
  incarnation := ⟨1⟩
  allocation := ⟨⟨2⟩,some (⟨3⟩,⟨1⟩)⟩
def ctx : Conditions := ⟨True,True,True,fun _ => True⟩
def noAuthority : Conditions := ⟨True,False,False,fun _ => False⟩
def after (k : Case) (a : Access) (deps ext : Finset Conditional.Fact) : State :=
  candidate geometry sites (before k a deps ext) (move k)

/-- Singleton fixed-root layout, with one conditional payload; other fixed
aggregate descendants are outside this bounded pre-existing conditional slice. -/
theorem singleton_invariant (s : Conditional.State) (l : RootLocationId) (n : Nat)
    (deps ext : Finset Conditional.Fact)
    (live : s.liveRoots = {l}) (active : s.root l = root l n)
    (values : s.values = (semantic deps ext).values)
    (loose : s.loosePackages = {external}) (types : s.types = (semantic deps ext).types)
    (domains : s.liveDomains = {⟨0⟩}) (carriers : s.domainValueCarrier = (semantic deps ext).domainValueCarrier)
    (inc : (⟨n⟩ : IncarnationId) ∈ s.usedIncarnations)
    (vf : (⟨2*n⟩ : ValueFactId) ∈ s.usedValueFacts) (pf : (⟨2*n+1⟩ : ValueFactId) ∈ s.usedValueFacts)
    (occ : (⟨n⟩ : Conditional.OccurrenceId) ∈ s.usedOccurrences) : Conditional.Invariant s := by
  have loc : ∀ m ∈ s.liveRoots, m = l := by intro m member; simpa [live] using member
  constructor
  · constructor
    · intro a al b bl _; exact (loc a al).trans (loc b bl).symm
    · intro a al b bl _; exact (loc a al).trans (loc b bl).symm
    · intro a al b bl _; exact (loc a al).trans (loc b bl).symm
    · intro a al b bl _; exact (loc a al).trans (loc b bl).symm
    · intro m ml; rw [loc m ml,active,loose]; simp [root,pkg,external]
    · intro m ml; rw [loc m ml,active,domains]; simp [root]
    · intro m ml; rw [loc m ml,active]; exact vf
    · intro m ml; rw [loc m ml,active]; exact inc
    · intro d; by_cases same : d = ⟨0⟩ <;> simp [domains,carriers,semantic,same]
  · intro p _; rw [values]; by_cases same : p = pkg <;> simp [semantic,same]
  · intro p _ v present
    by_cases same : p = pkg
    · subst p
      have eq : v = sumValue deps := by simpa [Conditional.sumAt,values,semantic,Conditional.SemanticValue.sumValue] using present.symm
      subst v; simp [Conditional.ValueTyped,types,semantic,sumValue]
    · simp [Conditional.sumAt,values,semantic,same,externalValue,Conditional.SemanticValue.sumValue] at present
  · intro m ml v present; rw [loc m ml,active] at present ⊢
    have eq : v = sumValue deps := by simpa [Conditional.sumAt,values,semantic,root,Conditional.SemanticValue.sumValue] using present.symm
    subst v; rfl
  · intro m ml; rw [loc m ml,active,values]; exact ⟨sumValue deps,by simp [semantic,root]⟩
  · intro m ml v present; rw [loc m ml,active] at present ⊢
    have eq : v = sumValue deps := by simpa [Conditional.sumAt,values,semantic,root,Conditional.SemanticValue.sumValue] using present.symm
    subst v; exact ⟨rfl,rfl⟩
  · intro a al b bl o _ _; exact (loc a al).trans (loc b bl).symm
  · intro m ml o eq; rw [loc m ml,active] at eq
    have same : (⟨n⟩ : Conditional.OccurrenceId) = o := Option.some.inj eq
    exact same ▸ occ
  · intro m ml fact eq; rw [loc m ml,active] at eq
    have same : (⟨2*n+1⟩ : ValueFactId) = fact := Option.some.inj eq
    exact same ▸ pf

theorem before_invariant (deps ext : Finset Conditional.Fact) : Conditional.Invariant (semantic deps ext) := by
  apply singleton_invariant (semantic deps ext) source 0 deps ext
  all_goals first | rfl | simp [semantic]

theorem after_invariant (k : Case) (a : Access) (deps ext : Finset Conditional.Fact) :
    Conditional.Invariant (after k a deps ext).accounted.base.semantic := by
  apply singleton_invariant _ destination 1 deps ext
  all_goals simp [after,candidate,semanticCandidate,movedRoot,Conditional.installRoot,move,before,semantic,
    root,sites,source,destination,Conditional.Allocation.facts,Conditional.Allocation.occurrences,Finset.pair_comm]

/-- Dependency-free post endpoints retain every inherited semantic obligation. -/
theorem independent_dependencies (s : Conditional.State)
    (values : s.values = (semantic ∅ ∅).values) : Conditional.DependenciesValid s := by
  intro p vLive v present f dep
  by_cases same : p = pkg
  · subst p
    have eq : v = .sum (sumValue ∅) := Option.some.inj (present.symm.trans (by simp [values,semantic]))
    subst v; simp [Conditional.SemanticValue.dependencies,Conditional.SumValue.dependencies,sumValue] at dep
  · have eq : v = externalValue ∅ := Option.some.inj (present.symm.trans (by simp [values,semantic,same]))
    subst v; simp [externalValue,Conditional.SemanticValue.dependencies] at dep

end
end NewLang.F1.Relocation.Counterexample
