import NewLang.F1.Backing.Current
import NewLang.F1.Backing.Lifetime
import NewLang.F1.Conditional.Counterexample.Sum

namespace NewLang.F1.Backing.Counterexample.Boundary
open F0
noncomputable section

private def region (n : Nat) : BackingRegionId := ⟨n⟩
private def byte (n : Nat) : AbstractByteId := ⟨n⟩
private def rw : Access := ⟨true,true⟩
private def wo : Access := ⟨false,true⟩
private def ro : Access := ⟨true,false⟩
private def placement (n : Nat) : Placement := ⟨region n,{byte n}⟩

/-- Concrete realization: one abstract byte and nominal region per live root.
This is a witness, not a runtime layout requirement. -/
private def annotate (roots : Finset RootLocationId) : PhysicalState where
  world := ⟨roots.image (fun l => region l.index), fun r => {byte r.index}, fun _ => rw⟩
  placement := fun l => if l ∈ roots then some (placement l.index) else none

private theorem singleton_disjoint {a b : Nat} (different : a ≠ b) :
    Disjoint ({byte a} : Finset AbstractByteId) {byte b} := by
  apply Finset.disjoint_left.mpr
  intro x left right
  have same := (Finset.mem_singleton.mp left).symm.trans (Finset.mem_singleton.mp right)
  exact different (congrArg AbstractByteId.index same)

private theorem annotation_wf (roots : Finset RootLocationId) :
    PhysicalWellFormed (fun l => l ∈ roots) (annotate roots) := by
  constructor
  · intro r _ q _ different
    apply singleton_disjoint
    intro eq; exact different (by cases r; cases q; cases eq; rfl)
  · intro l; by_cases live : l ∈ roots <;> simp [annotate,live]
  · intro l pl placed
    by_cases live : l ∈ roots
    · have eq : pl = placement l.index := by simpa [annotate,live] using placed.symm
      subst pl; exact Finset.mem_image.mpr ⟨l,live,rfl⟩
    · simp [annotate,live] at placed
  · intro l pl placed
    by_cases live : l ∈ roots
    · have eq : pl = placement l.index := by simpa [annotate,live] using placed.symm
      subst pl; exact Finset.Subset.refl _
    · simp [annotate,live] at placed
  · intro l m a b la mb different
    by_cases ll : l ∈ roots
    · by_cases ml : m ∈ roots
      · have ae : a = placement l.index := by simpa [annotate,ll] using la.symm
        have be : b = placement m.index := by simpa [annotate,ml] using mb.symm
        subst a; subst b; apply singleton_disjoint
        intro eq; exact different (by cases l; cases m; cases eq; rfl)
      · simp [annotate,ml] at mb
    · simp [annotate,ll] at la

private theorem annotation_write {roots : Finset RootLocationId} {l : RootLocationId}
    (live : l ∈ roots) : WriteAt (annotate roots) l :=
  ⟨placement l.index,by simp [annotate,live],rfl⟩

private def placedSum (s : Conditional.State) : SumState := ⟨s,annotate s.liveRoots⟩

private theorem placedSum_wf {s : Conditional.State} (wf : Conditional.WellFormed s) :
    SumWellFormed (placedSum s) := ⟨wf.toInvariant,wf.dependencies,annotation_wf _⟩

private theorem liftWhole {w ty : Prop} {s post : Conditional.State} {l incoming v a old}
    (step : Conditional.WholeStep w ty s l incoming v a old post) :
    WholeStep w ty (placedSum s) l incoming v a old ⟨post,(placedSum s).physical⟩ :=
  whole_lift_is_legal (placedSum_wf step.1) step (annotation_write step.2.1.target_live)

private theorem liftSwap {w ty : Prop} {s post : Conditional.State} {l r}
    (step : Conditional.SwapStep w ty s l r post) :
    SwapStep w ty (placedSum s) l r ⟨post,(placedSum s).physical⟩ := by
  have live : l ∈ s.liveRoots ∧ r ∈ s.liveRoots := by
    cases step.2.1 with
    | same h _ _ => exact ⟨h,h⟩
    | distinct raw => exact ⟨raw.left_live,raw.right_live⟩
  exact swap_lift_is_legal (placedSum_wf step.1) step (annotation_write live.1) (annotation_write live.2)

theorem every_conditional_wellFormed_state_has_backing {s : Conditional.State}
    (wf : Conditional.WellFormed s) : ∃ p, SumWellFormed ⟨s,p⟩ := ⟨_,placedSum_wf wf⟩

theorem independent_whole_replace_has_backing :
    ∃ s post l pkg v a, WholeStep True True s l pkg v a true post :=
  ⟨_,_,_,_,_,_,liftWhole Conditional.Counterexample.Sum.independent_whole_replace_is_legal⟩

theorem old_only_dependency_store_has_backing :
    ∃ s post l pkg v a, WholeStep True True s l pkg v a false post :=
  ⟨_,_,_,_,_,_,liftWhole Conditional.Counterexample.Sum.whole_store_eliminates_old_only_occurrence_dependency⟩

theorem independent_distinct_swap_has_backing :
    ∃ s post l r, l ≠ r ∧ SwapStep True True s l r post :=
  ⟨_,_,_,_,by decide,liftSwap Conditional.Counterexample.Sum.independent_distinct_sum_swap_is_legal⟩

theorem same_sum_swap_with_backing_is_exact_noop :
    ∃ s l, SwapStep True True s l l s :=
  ⟨_,_,liftSwap Conditional.Counterexample.Sum.same_place_sum_swap_is_exact_noop⟩

/-- A deliberately broken value-owned placement transfer still has well-formed
geometry. It violates the operation's frame law, not a random state invariant. -/
private def twoSites : PhysicalState := annotate {⟨0⟩,⟨1⟩}
private def exchangedPlacement : PhysicalState :=
  {twoSites with placement := fun l => if l = ⟨0⟩ then some (placement 1)
    else if l = ⟨1⟩ then some (placement 0) else none}

theorem distinct_placement_is_not_exchanged :
    twoSites.placement ⟨0⟩ ≠ twoSites.placement ⟨1⟩ := by
  simp [twoSites,annotate,placement,region,byte]

theorem broken_package_placement_exchange_breaks_frame :
    exchangedPlacement.placement ⟨0⟩ = twoSites.placement ⟨1⟩ ∧
    exchangedPlacement.placement ⟨0⟩ ≠ twoSites.placement ⟨0⟩ := by
  simp [exchangedPlacement,twoSites,annotate,placement,region,byte]

theorem broken_package_placement_exchange_is_geometrically_valid :
    PhysicalWellFormed (fun l => l ∈ ({⟨0⟩,⟨1⟩} : Finset RootLocationId)) exchangedPlacement := by
  constructor
  · exact (annotation_wf ({⟨0⟩,⟨1⟩} : Finset RootLocationId)).regions
  · intro l; by_cases a : l = ⟨0⟩ <;> by_cases b : l = ⟨1⟩ <;>
      simp [exchangedPlacement,a,b]
  · intro l pl placed; by_cases a : l = ⟨0⟩ <;> by_cases b : l = ⟨1⟩ <;>
      simp [exchangedPlacement,a,b] at placed <;> subst pl <;> simp [exchangedPlacement,twoSites,annotate,placement]
  · intro l pl placed; by_cases a : l = ⟨0⟩ <;> by_cases b : l = ⟨1⟩ <;>
      simp [exchangedPlacement,a,b] at placed <;> subst pl <;> exact Finset.Subset.refl _
  · intro l m a b la mb different
    by_cases l0 : l = ⟨0⟩ <;> by_cases l1 : l = ⟨1⟩ <;>
      by_cases m0 : m = ⟨0⟩ <;> by_cases m1 : m = ⟨1⟩ <;>
      simp [exchangedPlacement,l0,l1,m0,m1] at la mb <;>
      subst a <;> subst b <;> first
      | exact False.elim (different (l0.trans m0.symm))
      | exact False.elim (different (l1.trans m1.symm))
      | exact singleton_disjoint (by decide)

private def oneWorld (access : Access) : World :=
  ⟨{region 0}, fun r => {byte r.index}, fun _ => access⟩
private def onePhysical (access : Access) (active : Bool) : PhysicalState :=
  ⟨oneWorld access,fun l => if active ∧ l = ⟨0⟩ then some (placement 0) else none⟩
private def sites : RootSiteLayout := ⟨fun l => ⟨l.index⟩,by
  intro a b eq; exact congrArg (fun p : PlaceId => RootLocationId.mk p.index) eq⟩
private def root (n : Nat) : LiveRoot := initializeRoot sites ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨n⟩ ⟨n⟩
private def data : ValuePackage := ⟨∅,true⟩
private def semantic (active : Bool) (n : Nat) (loose : Finset PackageId)
    (history : Finset Nat) : F0.State where
  occupancy := fun l => if active ∧ l = ⟨0⟩ then .live (root n) else .vacant
  packages := fun _ => some data
  loosePackages := loose
  liveDomains := {⟨0⟩}
  domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
  usedValueFacts := history.image ValueFactId.mk
  usedIncarnations := history.image IncarnationId.mk

private theorem live_iff {active n loose history l r} :
    (semantic active n loose history).occupancy l = .live r ↔
    active = true ∧ l = ⟨0⟩ ∧ r = root n := by
  cases active <;> by_cases eq : l = ⟨0⟩ <;> simp [semantic,eq,eq_comm]

private theorem semantic_wf (active : Bool) (n : Nat) (loose : Finset PackageId) (history : Finset Nat)
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

private def flat (access : Access) (active : Bool) (n : Nat)
    (loose : Finset PackageId) (history : Finset Nat) : FlatState :=
  ⟨semantic active n loose history,onePhysical access active⟩

private theorem flat_wf (access : Access) (active : Bool) (n : Nat)
    (loose : Finset PackageId) (history : Finset Nat)
    (unique : active = true → (⟨0⟩ : PackageId) ∉ loose)
    (recorded : active = true → n ∈ history) : FlatWellFormed (flat access active n loose history) := by
  refine ⟨semantic_wf _ _ _ _ unique recorded,?_⟩
  change PhysicalWellFormed (FlatLive (semantic active n loose history)) (onePhysical access active)
  constructor
  · intro r rl q ql different
    have re : r = region 0 := Finset.mem_singleton.mp rl
    have qe : q = region 0 := Finset.mem_singleton.mp ql
    exact False.elim (different (re.trans qe.symm))
  · intro l; simp only [FlatLive,live_iff]
    cases active <;> by_cases eq : l = ⟨0⟩ <;> simp [onePhysical,eq]
  · intro l pl placed
    cases active <;> by_cases eq : l = ⟨0⟩ <;> simp [onePhysical,eq] at placed
    subst pl; simp [onePhysical,oneWorld,placement]
  · intro l pl placed
    cases active <;> by_cases eq : l = ⟨0⟩ <;> simp [onePhysical,eq] at placed
    subst pl; exact Finset.Subset.refl _
  · intro l m a b la mb different
    cases active <;> by_cases le : l = ⟨0⟩ <;> by_cases me : m = ⟨0⟩ <;>
      simp [onePhysical,le,me] at la mb
    exact False.elim (different (le.trans me.symm))

private def evidence (a : Access) : Evidence := ⟨region 0,a⟩
private def before (a : Access) : FlatState := flat a false 0 {⟨0⟩} ∅
private def first (a : Access) : FlatState := flat a true 1 ∅ {1}
private def taken (a : Access) : FlatState := flat a false 1 {⟨0⟩} {1}
private def destroyed (a : Access) : FlatState := flat a false 1 ∅ {1}
private def restarted (a : Access) : FlatState := flat a true 2 ∅ {1,2}
private def ptr (a : Access) : AccessPtr := initializePtr ⟨0⟩ ⟨1⟩ (evidence a)

private theorem first_raw (a : Access) (write : a.write = true) :
    RawInitialize sites True True (before a) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩
      (placement 0) (evidence a) (first a) := by
  constructor
  · refine ⟨rfl,by simp [before,flat,semantic],by simp [before,flat,semantic],?_,?_,trivial,trivial,?_⟩
    · simp [FreshIncarnation,before,flat,semantic]
    · simp [FreshValueFact,before,flat,semantic]
    · simp [first,before,flat,semantic,initializeCandidate,root,initializeRoot,sites]
  · exact ⟨by simp [before,flat,onePhysical,oneWorld,evidence],accessLe_refl a⟩
  · rfl
  · exact write
  · exact Finset.Subset.refl _
  · intro m pl placed; simp [before,flat,onePhysical] at placed
  · simp [first,before,flat,onePhysical,startPlacement]

private theorem first_current (a : Access) (write : a.write = true) : CurrentAccessPtr (first a) (ptr a) :=
  initialize_produces_current_ptr (first_raw a write)

private theorem take_raw : RawTake True (first rw) ⟨0⟩ (root 1) ⟨0⟩ (ptr rw) (taken rw) := by
  refine ⟨⟨by simp [first,flat,semantic],rfl,trivial,?_⟩,rfl,first_current rw rfl,rfl,?_⟩
  · simp [taken,first,flat,semantic,takeCandidate,root,initializeRoot,sites]
    funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
  · simp [taken,first,flat,onePhysical,endPlacement]
    funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]

private theorem destroy_raw : RawDestroy True (first wo) ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (destroyed wo) := by
  refine ⟨⟨by simp [first,flat,semantic],rfl,trivial,⟨data,rfl,rfl⟩,?_⟩,
    rfl,first_current wo rfl,?_⟩
  · simp [destroyed,first,flat,semantic,destroyCandidate,root,initializeRoot,sites]
    funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]
  · simp [destroyed,first,flat,onePhysical,endPlacement]
    funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]

private theorem restart_raw :
    RawInitialize sites True True (taken rw) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (placement 0) (evidence rw) (restarted rw) := by
  constructor
  · refine ⟨rfl,by simp [taken,flat,semantic],by simp [taken,flat,semantic],?_,?_,trivial,trivial,?_⟩
    · simp [FreshIncarnation,taken,flat,semantic]
    · simp [FreshValueFact,taken,flat,semantic]
    · simp [restarted,taken,flat,semantic,initializeCandidate,root,initializeRoot,sites,Finset.pair_comm]
  · exact ⟨by simp [taken,flat,onePhysical,oneWorld,evidence],accessLe_refl rw⟩
  · rfl
  · rfl
  · exact Finset.Subset.refl _
  · intro m pl placed; simp [taken,flat,onePhysical] at placed
  · simp [restarted,taken,flat,onePhysical,startPlacement]

theorem readwrite_initialize_is_legal :
    InitializeStep sites True True (before rw) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩
      (placement 0) (evidence rw) (first rw) :=
  ⟨flat_wf _ _ _ _ _ (by simp) (by simp),first_raw rw rfl,
    flat_wf _ _ _ _ _ (by simp) (by simp)⟩

theorem writeonly_initialize_is_legal :
    InitializeStep sites True True (before wo) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩
      (placement 0) (evidence wo) (first wo) :=
  ⟨flat_wf _ _ _ _ _ (by simp) (by simp),first_raw wo rfl,
    flat_wf _ _ _ _ _ (by simp) (by simp)⟩

theorem readwrite_take_is_legal :
    TakeStep True (first rw) ⟨0⟩ (root 1) ⟨0⟩ (ptr rw) (taken rw) :=
  ⟨readwrite_initialize_is_legal.2.2,take_raw,flat_wf _ _ _ _ _ (by simp) (by simp)⟩

theorem writeonly_destroy_is_legal :
    DestroyStep True (first wo) ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (destroyed wo) :=
  ⟨writeonly_initialize_is_legal.2.2,destroy_raw,flat_wf _ _ _ _ _ (by simp) (by simp)⟩

theorem writeonly_take_is_rejected :
    ¬ RawTake True (first wo) ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (taken wo) :=
  take_rejects_writeonly_ptr rfl

theorem readonly_initialize_is_rejected :
    ¬ RawInitialize sites True True (before ro) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩
      (placement 0) (evidence ro) (first ro) := initialize_rejects_readonly_region rfl

/-- Deliberately broken end rule, isolated from the kernel. -/
private def BrokenDestroy (s : FlatState) (p : AccessPtr) (post : FlatState) : Prop :=
  DestroyStep True s ⟨0⟩ (root 1) ⟨0⟩ p post ∧ p.evidence.access.read = true

theorem broken_destroy_read_guard_rejects_valid_language_case :
    DestroyStep True (first wo) ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (destroyed wo) ∧
    ¬ BrokenDestroy (first wo) (ptr wo) (destroyed wo) := by
  refine ⟨writeonly_destroy_is_legal,?_⟩
  rintro ⟨_,read⟩; cases read

theorem same_placement_restart_is_legal_but_old_ptr_is_stale :
    InitializeStep sites True True (taken rw) ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (placement 0) (evidence rw) (restarted rw) ∧
    (first rw).physical.placement ⟨0⟩ = (restarted rw).physical.placement ⟨0⟩ ∧
    ¬ CurrentAccessPtr (restarted rw) (ptr rw) := by
  refine ⟨⟨readwrite_take_is_legal.2.2,restart_raw,flat_wf _ _ _ _ _ (by simp) (by simp)⟩,
    rfl,take_then_restart_rejects_old_ptr readwrite_take_is_legal.1 take_raw restart_raw⟩

/-- Every start obligation except ordinary write holds in the read-only control. -/
theorem readonly_control_isolates_write_applicability :
    FlatWellFormed (before ro) ∧ FlatWellFormed (first ro) ∧
    F0.RawInitialize sites True True (before ro).semantic ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩ (first ro).semantic ∧
    EvidenceValid (before ro).physical.world (evidence ro) ∧
    (placement 0).region = (evidence ro).region ∧
    (placement 0).occupied ⊆ (before ro).physical.world.bytes (placement 0).region ∧
    (∀ m pl, (before ro).physical.placement m = some pl → Disjoint (placement 0).occupied pl.occupied) ∧
    (first ro).physical = startPlacement (before ro).physical ⟨0⟩ (placement 0) ∧
    (evidence ro).access.write = false := by
  refine ⟨flat_wf _ _ _ _ _ (by simp) (by simp),flat_wf _ _ _ _ _ (by simp) (by simp),
    (first_raw rw rfl).semantic,⟨by simp [before,flat,onePhysical,oneWorld,evidence],accessLe_refl ro⟩,
    rfl,Finset.Subset.refl _,?_,?_,rfl⟩
  · intro m pl placed; simp [before,flat,onePhysical] at placed
  · simp [first,before,flat,onePhysical,startPlacement]

theorem writeonly_take_control_isolates_read_applicability :
    FlatWellFormed (first wo) ∧ FlatWellFormed (taken wo) ∧
    F0.RawTake True (first wo).semantic ⟨0⟩ (root 1) ⟨0⟩ (taken wo).semantic ∧
    CurrentAccessPtr (first wo) (ptr wo) ∧
    (taken wo).physical = endPlacement (first wo).physical ⟨0⟩ ∧
    ¬ RawTake True (first wo) ⟨0⟩ (root 1) ⟨0⟩ (ptr wo) (taken wo) :=
  ⟨writeonly_initialize_is_legal.2.2,flat_wf _ _ _ _ _ (by simp) (by simp),
    take_raw.semantic,first_current wo rfl,(by
      simp [taken,first,flat,onePhysical,endPlacement]
      funext l; by_cases eq : l = ⟨0⟩ <;> simp [eq]),writeonly_take_is_rejected⟩

theorem stronger_ptr_evidence_is_rejected :
    CurrentAccessPtr (first wo) (ptr wo) ∧
    ¬ EvidenceValid (first wo).physical.world (evidence rw) := by
  refine ⟨first_current wo rfl,?_⟩
  intro valid; have read := evidence_cannot_amplify_read valid rfl; cases read

private def deadBacking : PhysicalState :=
  {(first rw).physical with world := {(first rw).physical.world with liveRegions := ∅}}

theorem dead_backing_control_isolates_region_liveness :
    F0.WellFormed (first rw).semantic ∧ RegionsDisjoint deadBacking.world ∧
    (∀ l, FlatLive (first rw).semantic l ↔ ∃ pl, deadBacking.placement l = some pl) ∧
    (∀ l pl, deadBacking.placement l = some pl → pl.occupied ⊆ deadBacking.world.bytes pl.region) ∧
    (∀ l m a b, deadBacking.placement l = some a → deadBacking.placement m = some b →
      l ≠ m → Disjoint a.occupied b.occupied) ∧
    ¬ PhysicalWellFormed (FlatLive (first rw).semantic) deadBacking := by
  have wf := readwrite_initialize_is_legal.2.2
  refine ⟨flat_wellFormed_erases_to_f0 wf,?_,wf.backing.exact,wf.backing.extent,wf.backing.rootsDisjoint,?_⟩
  · simp [RegionsDisjoint,deadBacking]
  · intro broken
    have live := broken.regionLive ⟨0⟩ (placement 0) (by simp [deadBacking,first,flat,onePhysical])
    exact Finset.notMem_empty _ live

/-- A hypothetical address label is deliberately not a state identity/authority. -/
private def hypotheticalAddress (_ : BackingRegionId) : Nat := 4096

theorem equal_hypothetical_addresses_do_not_identify_regions :
    hypotheticalAddress (region 0) = hypotheticalAddress (region 1) ∧ region 0 ≠ region 1 :=
  ⟨rfl,by decide⟩

/-- A consumed source value is installed at an explicitly supplied different region. -/
private def transferSource : FlatState :=
  {(taken rw) with physical := ⟨twoSites.world,fun _ => none⟩}
private def transferPost (n : Nat) : FlatState :=
  {(restarted rw) with physical := ⟨twoSites.world,fun l => if l = ⟨0⟩ then some (placement n) else none⟩}

private theorem transfer_source_wf : FlatWellFormed transferSource := by
  have semanticWF := flat_wellFormed_erases_to_f0 readwrite_take_is_legal.2.2
  refine ⟨semanticWF,?_⟩
  constructor
  · exact (annotation_wf ({⟨0⟩,⟨1⟩} : Finset RootLocationId)).regions
  · intro l; simp [transferSource,taken,flat,semantic,FlatLive]
  · intro l pl placed; cases placed
  · intro l pl placed; cases placed
  · intro l m a b placed; cases placed

private theorem transfer_post_wf (n : Nat) (live : n = 0 ∨ n = 1) : FlatWellFormed (transferPost n) := by
  have semanticWF := flat_wellFormed_erases_to_f0 (flat_wf rw true 2 ∅ {1,2} (by simp) (by simp))
  refine ⟨semanticWF,?_⟩
  constructor
  · exact (annotation_wf ({⟨0⟩,⟨1⟩} : Finset RootLocationId)).regions
  · intro l; simp only [transferPost,restarted,flat,FlatLive,live_iff]
    by_cases eq : l = ⟨0⟩ <;> simp [eq]
  · intro l pl placed
    by_cases eq : l = ⟨0⟩
    · have pe : pl = placement n := by simpa [transferPost,eq] using placed.symm
      subst pl; rcases live with rfl|rfl <;> simp [transferPost,twoSites,annotate,placement]
    · simp [transferPost,eq] at placed
  · intro l pl placed
    by_cases eq : l = ⟨0⟩
    · have pe : pl = placement n := by simpa [transferPost,eq] using placed.symm
      subst pl; exact Finset.Subset.refl _
    · simp [transferPost,eq] at placed
  · intro l m a b la mb different
    by_cases le : l = ⟨0⟩ <;> by_cases me : m = ⟨0⟩ <;> simp [transferPost,le,me] at la mb
    exact False.elim (different (le.trans me.symm))

private theorem transfer_raw :
    RawInitialize sites True True transferSource ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (placement 1) ⟨region 1,rw⟩ (transferPost 1) := by
  constructor
  · exact restart_raw.semantic
  · exact ⟨by simp [transferSource,twoSites,annotate],accessLe_refl rw⟩
  · rfl
  · rfl
  · exact Finset.Subset.refl _
  · intro m pl placed; cases placed
  · simp [transferPost,transferSource,startPlacement]

theorem value_transfer_installs_at_destination_not_source :
    InitializeStep sites True True transferSource ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (placement 1) ⟨region 1,rw⟩ (transferPost 1) ∧
    (first rw).semantic.packages ⟨0⟩ = (transferPost 1).semantic.packages ⟨0⟩ ∧
    (first rw).physical.placement ⟨0⟩ ≠ (transferPost 1).physical.placement ⟨0⟩ := by
  refine ⟨⟨transfer_source_wf,transfer_raw,transfer_post_wf 1 (Or.inr rfl)⟩,rfl,?_⟩
  simp [first,flat,onePhysical,transferPost,placement,region,byte]

/-- Deliberately wrong ownership: a value carries its source placement. -/
private structure BrokenPlacedValue where
  value : ValuePackage
  sourcePlacement : Placement

private def brokenTransferredValue : BrokenPlacedValue := ⟨data,placement 0⟩
private def brokenValueOwnedCandidate : FlatState :=
  {(restarted rw) with physical := ⟨twoSites.world,fun l =>
    if l = ⟨0⟩ then some brokenTransferredValue.sourcePlacement else none⟩}

theorem broken_value_owned_source_placement_is_rejected :
    FlatWellFormed brokenValueOwnedCandidate ∧
    brokenValueOwnedCandidate.semantic = (transferPost 1).semantic ∧
    ¬ RawInitialize sites True True transferSource ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨2⟩ ⟨2⟩
      (placement 1) ⟨region 1,rw⟩ brokenValueOwnedCandidate := by
  refine ⟨transfer_post_wf 0 (Or.inl rfl),rfl,?_⟩
  intro raw
  have placed := (initialize_uses_destination_placement raw).1
  simp [brokenValueOwnedCandidate,brokenTransferredValue,placement,region,byte] at placed


theorem swap_rejects_package_owned_placement_exchange (s post : Conditional.State) :
    ¬ RawSwap True True ⟨s,twoSites⟩ ⟨0⟩ ⟨1⟩ ⟨post,exchangedPlacement⟩ := by
  intro raw
  have frame := congrArg (fun p : PhysicalState => p.placement ⟨0⟩) raw.physical
  exact broken_package_placement_exchange_breaks_frame.2 frame


theorem broken_swap_control_keeps_semantics_and_geometry_valid :
    ∃ s post, Conditional.SwapStep True True s ⟨0⟩ ⟨1⟩ post ∧
      SumWellFormed ⟨s,twoSites⟩ ∧ SumWellFormed ⟨post,exchangedPlacement⟩ ∧
      ¬ RawSwap True True ⟨s,twoSites⟩ ⟨0⟩ ⟨1⟩ ⟨post,exchangedPlacement⟩ := by
  have step := Conditional.Counterexample.Sum.independent_distinct_sum_swap_is_legal
  exact ⟨_,_,step,placedSum_wf step.1,
    ⟨step.2.2.toInvariant,step.2.2.dependencies,broken_package_placement_exchange_is_geometrically_valid⟩,
    swap_rejects_package_owned_placement_exchange _ _⟩

end
end NewLang.F1.Backing.Counterexample.Boundary
