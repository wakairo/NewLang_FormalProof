import NewLang.F1.Occupancy.Lifetime

namespace NewLang.F1.Occupancy.Counterexample
open F0 Backing
noncomputable section

-- Four abstract bytes in a single live region; coordinates are relative ordinals.
def region (n : Nat) : BackingRegionId := ⟨n⟩
def cid (n : Nat) : ClaimId := ⟨n⟩
def rw : Access := ⟨true,true⟩
def wo : Access := ⟨false,true⟩
def ro : Access := ⟨true,false⟩
def geometry : Geometry := ⟨fun _ => 4,fun r n => ⟨r.index*8+n⟩,by
  intro r a b eq
  have indices := congrArg AbstractByteId.index eq
  change r.index*8+a = r.index*8+b at indices
  omega⟩
def layout : Layout := ⟨fun t => t.index+1,by intro t; omega⟩
def ty : TypeId := ⟨1⟩
def full : Extent := ⟨region 0,⟨0,4⟩⟩
def left : Extent := full.left 2
def right : Extent := full.right 2
def world (a : Access) : World :=
  ⟨{region 0},fun r => (Finset.range 4).image (geometry.byteAt r),fun _ => a⟩
def physical (a : Access) (active : Bool) : PhysicalState :=
  ⟨world a,fun l => if active ∧ l = ⟨0⟩ then some (left.placement geometry) else none⟩

def sites : RootSiteLayout := ⟨fun l => ⟨l.index⟩,by
  intro a b eq; exact congrArg (fun p : PlaceId => RootLocationId.mk p.index) eq⟩
def root (n : Nat) : LiveRoot := initializeRoot sites ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨n⟩ ⟨n⟩
def data : ValuePackage := ⟨∅,true⟩
def semantic (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) : F0.State where
  occupancy := fun l => if active ∧ l = ⟨0⟩ then .live (root n) else .vacant
  packages := fun _ => some data
  loosePackages := loose
  liveDomains := {⟨0⟩}
  domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
  usedValueFacts := history.image ValueFactId.mk
  usedIncarnations := history.image IncarnationId.mk

theorem live_iff {active n loose history l r} :
    (semantic active n loose history).occupancy l = .live r ↔
    active = true ∧ l = ⟨0⟩ ∧ r = root n := by
  cases active <;> by_cases eq : l = ⟨0⟩ <;> simp [semantic,eq,eq_comm]

theorem semantic_wf (active : Bool) (n : Nat) (loose : Finset PackageId) (history : Finset Nat)
    (unique : active = true → (⟨0⟩ : PackageId) ∉ loose)
    (recorded : active = true → n ∈ history) : F0.WellFormed (semantic active n loose history) := by
  constructor
  · intro pkg c1 c2 h1 h2
    cases c1 <;> cases c2 <;> simp only [Carries,live_iff] at h1 h2
    · rcases h1 with ⟨r,⟨_,le,_⟩,_⟩; rcases h2 with ⟨q,⟨_,me,_⟩,_⟩
      exact congrArg Carrier.installed (le.trans me.symm)
    · rcases h1 with ⟨r,⟨a,_,rEq⟩,pEq⟩; subst r
      have pkgEq : pkg = ⟨0⟩ := pEq.symm
      subst pkg; exact False.elim (unique a h2)
    · rcases h2 with ⟨r,⟨a,_,rEq⟩,pEq⟩; subst r
      have pkgEq : pkg = ⟨0⟩ := pEq.symm
      subst pkg; exact False.elim (unique a h1)
    · rfl
  · intro l m a b la mb _; rcases live_iff.mp la with ⟨_,le,_⟩
    rcases live_iff.mp mb with ⟨_,me,_⟩; exact le.trans me.symm
  · intro l m a b la mb _; rcases live_iff.mp la with ⟨_,le,_⟩
    rcases live_iff.mp mb with ⟨_,me,_⟩; exact le.trans me.symm
  · intro pkg _; exact ⟨data,rfl⟩
  · intro l r live; rcases live_iff.mp live with ⟨_,_,rfl⟩; simp [semantic,root,initializeRoot]
  · intro pkg value _ present fact dep
    have eq : value = data := Option.some.inj present.symm; subst value
    exact False.elim (Finset.notMem_empty _ dep)
  · intro l r live; rcases live_iff.mp live with ⟨yes,_,rfl⟩
    exact Finset.mem_image.mpr ⟨n,recorded yes,rfl⟩
  · intro l r live; rcases live_iff.mp live with ⟨yes,_,rfl⟩
    exact Finset.mem_image.mpr ⟨n,recorded yes,rfl⟩
  · intro d; by_cases same : d = ⟨0⟩ <;> simp [semantic,same]


def flat (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) : FlatState := ⟨semantic active n loose history,physical a active⟩

/-- The non-root right half is retained throughout the entire lifecycle. -/
def rawLedger : Ledger := ⟨{region 0},{cid 0},fun _ => .storage full⟩
def splitLedger : Ledger := splitCandidate rawLedger (cid 0) (cid 1) (cid 20) full 2
def slotLedger : Ledger := consumeOne splitLedger (cid 1) (cid 3) (.slot ty left)
def liveLedger : Ledger := consumeOne slotLedger (cid 3) (cid 4) (.root ty ⟨0⟩ left)
def takenLedger : Ledger := consumeOne liveLedger (cid 4) (cid 5) (.slot ty left)
def restartLedger : Ledger := consumeOne takenLedger (cid 5) (cid 6) (.root ty ⟨0⟩ left)
def endLedger : Ledger := consumeOne restartLedger (cid 6) (cid 7) (.slot ty left)
def erasedLedger : Ledger := consumeOne endLedger (cid 7) (cid 8) (.storage left)
def mergedLedger : Ledger := mergeCandidate erasedLedger (cid 8) (cid 20) (cid 9) left right

def rawState : State := ⟨flat rw false 0 {⟨0⟩} ∅,rawLedger⟩
def splitState : State := ⟨rawState.flat,splitLedger⟩
def slotState (a : Access) : State := ⟨flat a false 0 {⟨0⟩} ∅,slotLedger⟩
def first (a : Access) : State := ⟨flat a true 1 ∅ {1},liveLedger⟩
def taken (a : Access) : State := ⟨flat a false 1 {⟨0⟩} {1},takenLedger⟩
def restarted : State := ⟨flat rw true 2 ∅ {1,2},restartLedger⟩
def ended : State := ⟨flat rw false 2 ∅ {1,2},endLedger⟩
def erased : State := ⟨ended.flat,erasedLedger⟩
def merged : State := ⟨ended.flat,mergedLedger⟩
def evidence (a : Access) : Evidence := ⟨region 0,a⟩
def ptr (a : Access) : AccessPtr := initializePtr ⟨0⟩ ⟨1⟩ (evidence a)
def secondPtr : AccessPtr := initializePtr ⟨0⟩ ⟨2⟩ (evidence rw)

def halfClaim (active : Bool) : Claim :=
  if active then .root ty ⟨0⟩ left else .slot ty left

/-- All shape obligations are independent of inactive table entries. -/
theorem pair_shape (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId) (c : Claim)
    (scope : s.scope = {region 0}) (ids : s.active = {id,cid 20}) (different : id ≠ cid 20)
    (lc : s.claim id = c) (rc : s.claim (cid 20) = .storage right)
    (extent : c.extent = left) (typed : c.Typed layout)
    (rootClaim : ∀ t l e, c = .root t l e ↔ active = true ∧ t = ty ∧ l = ⟨0⟩ ∧ e = left) :
    AccountingShape geometry layout (FlatLive (semantic active n loose history)) (physical a active) s := by
  have classify : ∀ i ∈ s.active, i = id ∨ i = cid 20 := by
    intro i member; simpa [ids] using member
  have lcExtent : (s.claim id).extent = left := by rw [lc,extent]
  constructor
  · intro r; rfl
  · intro r rl q ql neq
    exact False.elim (neq ((Finset.mem_singleton.mp rl).trans (Finset.mem_singleton.mp ql).symm))
  · intro r member; simpa [scope,physical,world] using member
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent,scope]; exact Finset.mem_singleton_self _
    · rw [rc,scope]; exact Finset.mem_singleton.mpr (by rfl)
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent]; decide
    · rw [rc]; decide
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lcExtent]; change 2 ≤ 4; decide
    · rw [rc]; change 4 ≤ 4; decide
  · intro i member; rcases classify i member with rfl|rfl
    · rw [lc]; exact typed
    · simp [rc,Claim.Typed]
  · intro l; constructor
    · rintro ⟨r,h⟩; rcases live_iff.mp h with ⟨act,le,_⟩
      exact ⟨id,by simp [ids],ty,left,lc.trans ((rootClaim ty l left).mpr ⟨act,rfl,le,rfl⟩)⟩
    · rintro ⟨i,member,t,e,claim⟩
      rcases classify i member with rfl|rfl
      · rw [lc] at claim
        rcases (rootClaim t l e).mp claim with ⟨act,_,le,_⟩
        exact ⟨root n,live_iff.mpr ⟨act,le,rfl⟩⟩
      · simp [rc] at claim
  · intro l pl; constructor
    · intro placed
      have act : active = true := by cases active <;> simp [physical] at placed ⊢
      have loc : l = ⟨0⟩ := by by_cases eq : l = ⟨0⟩ <;> simp [physical,act,eq] at placed ⊢
      have pe : left.placement geometry = pl := by simpa [physical,act,loc] using placed
      exact ⟨id,by simp [ids],ty,left,lc.trans ((rootClaim ty l left).mpr ⟨act,rfl,loc,rfl⟩),pe⟩
    · rintro ⟨i,member,t,e,claim,pe⟩
      rcases classify i member with rfl|rfl
      · rw [lc] at claim
        rcases (rootClaim t l e).mp claim with ⟨act,_,le,ee⟩
        simpa [physical,act,le,ee] using congrArg some pe
      · simp [rc] at claim

theorem pair_accounting (a : Access) (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) (s : Ledger) (id : ClaimId) (c : Claim)
    (scope : s.scope = {region 0}) (ids : s.active = {id,cid 20}) (different : id ≠ cid 20)
    (lc : s.claim id = c) (rc : s.claim (cid 20) = .storage right)
    (extent : c.extent = left) (typed : c.Typed layout)
    (rootClaim : ∀ t l e, c = .root t l e ↔ active = true ∧ t = ty ∧ l = ⟨0⟩ ∧ e = left) :
    Accounting geometry layout (FlatLive (semantic active n loose history)) (physical a active) s := by
  refine ⟨pair_shape a active n loose history s id c scope ids different lc rc extent typed rootClaim,?_,?_⟩
  · intro i ia j ja neq
    have ic : i = id ∨ i = cid 20 := by simpa [ids] using ia
    have jc : j = id ∨ j = cid 20 := by simpa [ids] using ja
    rcases ic with rfl|rfl <;> rcases jc with rfl|rfl
    · exact False.elim (neq rfl)
    · rw [lc,rc,extent,Claim.extent]
      exact split_extents_disjoint geometry full 2
    · rw [lc,rc,extent,Claim.extent]
      exact (split_extents_disjoint geometry full 2).symm
    · exact False.elim (neq rfl)
  · have partition : left.footprint geometry ∪ right.footprint geometry = full.footprint geometry :=
      split_extents_exact_union geometry (by decide)
    have total : TotalFootprint geometry s = left.footprint geometry ∪ right.footprint geometry := by
      have leftEq : (s.claim id).extent.footprint geometry = left.footprint geometry := by rw [lc,extent]
      have rightEq : (s.claim (cid 20)).extent.footprint geometry = right.footprint geometry := by rw [rc]; rfl
      simp [TotalFootprint,ids,leftEq,rightEq]
    rw [total]
    simpa [ExpectedFootprint,scope,physical,world,Extent.footprint,full,Range.positions,Range.finish] using partition

end
end NewLang.F1.Occupancy.Counterexample
