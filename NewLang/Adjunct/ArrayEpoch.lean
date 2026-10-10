import NewLang.F1.Relocation.Proofs

/-! Issue #45: an UNSELECTED allocator-boundary transition experiment.
This finite projection is not a platform contract, admitted source API, or
simulation of every rich NewLang invariant. No post-invariant is a premise.
Numeric addresses are observable labels, never identity/freshness evidence. -/
namespace NewLang.Adjunct.ArrayEpoch
open F0 F1.Backing
noncomputable section

structure AllocationId where
  index : Nat
  deriving DecidableEq, Repr
structure KeeperId where
  index : Nat
  deriving DecidableEq, Repr

/-- One allocation epoch. Generations are ghost labels, not runtime counters. -/
structure Epoch where
  generation : Nat
  address : Nat
  capacity : Nat
  domain : DomainId
  deriving DecidableEq, Repr

def region (e : Epoch) : BackingRegionId := ⟨e.generation⟩
def allocation (e : Epoch) : AllocationId := ⟨e.generation⟩
def keeper (e : Epoch) : KeeperId := ⟨e.generation⟩
def size (e : Epoch) := 32 + 8 * e.capacity

def incarnation (e : Epoch) (i : Nat) : IncarnationId := ⟨32 * e.generation + i⟩
def token (e : Epoch) (i : Nat) : PtrToken :=
  ⟨⟨32 * e.generation + i⟩,incarnation e i⟩

def Supported (c : Nat) : Prop := c = 4 ∨ c = 8 ∨ c = 16
instance (c : Nat) : Decidable (Supported c) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Opaque affine value identity. Element representation bytes are not modelled.
No payload dependency or destructor theorem is claimed by this projection. -/
structure Package where
  id : PackageId
  data : Nat
  deriving DecidableEq, Repr

structure State where
  current : Option Epoch
  ownerCredits : List Nat
  values : List Package
  returned : List Package
  len : Nat
  cap : Nat
  used : Finset Nat
  releases : List Nat
  loans : Finset DomainId
  endingDomains : Finset DomainId
  deriving DecidableEq

/-- Current root descriptors are derived from one epoch and an ordered live list.
The list is proof state, not a runtime per-element registry. Header is RAW-owned.
Vacant tail is [32+8*n,32+8*cap), not an extra Allocation or zero-length Storage. -/
def CurrentRoot (s : State) (p : PtrToken) (d : DomainId) : Prop :=
  ∃ e, s.current = some e ∧ d = e.domain ∧
    ∃ i < s.values.length, p = token e i

def CurrentSpan (s : State) (e : Epoch) (count : Nat) : Prop :=
  s.current = some e ∧ count ≤ s.values.length ∧ e.domain ∈ s.loans

def ActiveInvariant (s : State) : Prop :=
  match s.current with
  | none => s.ownerCredits = [] ∧ s.values = [] ∧ s.len = 0 ∧ s.cap = 0
  | some e => s.ownerCredits = [e.generation] ∧ Supported e.capacity ∧
      s.len = s.values.length ∧ s.cap = e.capacity ∧ s.values.length ≤ e.capacity ∧
      e.generation ∈ s.used ∧ e.generation ∉ s.releases

instance (s : State) : Decidable (ActiveInvariant s) := by
  unfold ActiveInvariant
  cases s.current <;> infer_instance

structure WellFormed (s : State) : Prop where
  active : ActiveInvariant s
  uniqueValues : ((s.values ++ s.returned).map Package.id).Nodup
  uniqueReleases : s.releases.Nodup
  recordedReleases : ∀ g ∈ s.releases, g ∈ s.used

structure Request where
  generation : Nat
  address : Nat
  capacity : Nat
  deriving DecidableEq, Repr

def nextEpoch (old : Epoch) (r : Request) : Epoch :=
  ⟨r.generation,r.address,r.capacity,old.domain⟩

def candidate (s : State) (old : Epoch) (r : Request) : State :=
  {s with
    current := some (nextEpoch old r)
    ownerCredits := [r.generation]
    cap := r.capacity
    used := insert r.generation s.used
    releases := old.generation :: s.releases }

/-- Local conceptual grow premises; allocator refinement is NOT supplied by this
relation. All element values are transported exactly once by the constructor.
No post-WF, desired conservation, same-address stability or successful libc
realloc assertion appears as a premise. -/
structure Grow (s : State) (old : Epoch) (r : Request) : Prop where
  pre : WellFormed s
  current : s.current = some old
  closed : s.loans = ∅
  ending : old.domain ∈ s.endingDomains
  fresh : r.generation ∉ s.used
  supported : Supported r.capacity
  larger : old.capacity < r.capacity

inductive Outcome where | failure | success
  deriving DecidableEq, Repr

def execute (s : State) (old : Epoch) (r : Request) : Outcome → State
  | .failure => s
  | .success => candidate s old r

private theorem old_invariant {s old r} (g : Grow s old r) :
    s.ownerCredits = [old.generation] ∧ Supported old.capacity ∧
    s.len = s.values.length ∧ s.cap = old.capacity ∧ s.values.length ≤ old.capacity ∧
    old.generation ∈ s.used ∧ old.generation ∉ s.releases := by
  simpa [ActiveInvariant,g.current] using g.pre.active

theorem grow_preserves_wellFormed {s old r} (g : Grow s old r) :
    WellFormed (candidate s old r) := by
  have h := old_invariant g
  constructor
  · simp only [ActiveInvariant,candidate,nextEpoch]
    refine ⟨True.intro,g.supported,h.2.2.1,True.intro,
      le_trans h.2.2.2.2.1 (Nat.le_of_lt g.larger),by simp,?_⟩
    simp only [List.mem_cons,not_or]
    refine ⟨?_,?_⟩
    · intro eq; exact g.fresh (eq ▸ h.2.2.2.2.2.1)
    · intro mem; exact g.fresh (g.pre.recordedReleases _ mem)
  · exact g.pre.uniqueValues
  · exact List.nodup_cons.mpr ⟨h.2.2.2.2.2.2,g.pre.uniqueReleases⟩
  · intro x mem
    simp only [candidate,List.mem_cons] at mem
    rcases mem with rfl|mem
    · exact Finset.mem_insert_of_mem h.2.2.2.2.2.1
    · exact Finset.mem_insert_of_mem (g.pre.recordedReleases _ mem)

theorem failed_grow_is_exact_identity (s old r) : execute s old r .failure = s := rfl

theorem all_outcomes_wellFormed {s old r} (g : Grow s old r) (o : Outcome) :
    WellFormed (execute s old r o) := by
  cases o
  · exact g.pre
  · exact grow_preserves_wellFormed g

theorem successful_grow_transports_values_exactly_once (s old r) :
    (candidate s old r).values = s.values ∧ (candidate s old r).returned = s.returned := ⟨rfl,rfl⟩

theorem successful_grow_consumes_old_owner {s old r} (g : Grow s old r) :
    (candidate s old r).ownerCredits = [r.generation] ∧
    old.generation ∉ (candidate s old r).ownerCredits ∧
    (candidate s old r).releases = old.generation :: s.releases := by
  refine ⟨rfl,?_,rfl⟩
  simp only [candidate,List.mem_cons,List.not_mem_nil,or_false]
  intro eq; exact g.fresh (eq ▸ (old_invariant g).2.2.2.2.2.1)

theorem history_monotone (s old r) : s.used ⊆ (candidate s old r).used :=
  Finset.subset_insert _ _

theorem grow_preserves_governing_domain (old r) : (nextEpoch old r).domain = old.domain := rfl

theorem fresh_elements_have_new_incarnations {s old r} (g : Grow s old r)
    (i j : Nat) (hi : i < s.values.length) (hj : j < 16) :
    incarnation (nextEpoch old r) i ≠ incarnation old j := by
  have h := old_invariant g
  have cap : old.capacity ≤ 16 := by rcases h.2.1 with a|a|a <;> omega
  have different : r.generation ≠ old.generation := fun eq => g.fresh (eq ▸ h.2.2.2.2.2.1)
  intro eq
  have nums := congrArg IncarnationId.index eq
  simp only [incarnation,nextEpoch] at nums
  omega

theorem old_ptr_cannot_be_reacquired {s old r} (g : Grow s old r)
    (j : Nat) (hj : j < 16) : ¬ CurrentRoot (candidate s old r) (token old j) old.domain := by
  rintro ⟨e,eq,_,i,hi,pt⟩
  have same : e = nextEpoch old r := (Option.some.inj eq).symm
  subst e
  have inc := congrArg PtrToken.incarnation pt
  exact fresh_elements_have_new_incarnations g i j hi hj inc.symm

theorem fresh_root_is_current {s old r} (_g : Grow s old r) (i : Nat)
    (hi : i < s.values.length) :
    CurrentRoot (candidate s old r) (token (nextEpoch old r) i) old.domain :=
  ⟨nextEpoch old r,rfl,rfl,i,hi,rfl⟩

theorem span_blocks_grow {s old r} (outstanding : old.domain ∈ s.loans) : ¬ Grow s old r := by
  intro g; rw [g.closed] at outstanding; simp at outstanding

theorem history_reuse_blocks_grow {s old r} (used : r.generation ∈ s.used) : ¬ Grow s old r :=
  fun g => g.fresh used

/-- Affine take of every live value to explicit result custody; not implicit Drop.
This is an experimental list operation, NOT a full rich lifetime theorem. -/
def takeAll (s : State) : State :=
  {s with values := [], returned := s.values ++ s.returned, len := 0}

def RawRecoverable (s : State) (e : Epoch) : Prop :=
  s.current = some e ∧ s.values = [] ∧ s.loans = ∅

def freeCandidate (s : State) (e : Epoch) : State :=
  {s with
    current := none
    ownerCredits := []
    cap := 0
    releases := e.generation :: s.releases}

def Free (s : State) (e : Epoch) : Prop := WellFormed s ∧ RawRecoverable s e

theorem free_requires_no_live_child {s e} (f : Free s e) : s.values = [] := f.2.2.1

theorem free_requires_closed_scopes {s e} (f : Free s e) : s.loans = ∅ := f.2.2.2

theorem free_cannot_be_repeated (s e q) : ¬ Free (freeCandidate s e) q := by
  intro f; have eq := f.2.1; cases eq

/-- A scalar metadata update cannot supply an extra current element. -/
theorem metadata_cannot_mint_root (s : State) (n c : Nat) (p d) :
    CurrentRoot {s with len := n,cap := c} p d ↔ CurrentRoot s p d := Iff.rfl

/-- Safe projection has one live backing; actual byte identity belongs to geometry,
not this observable address label. This connects to the accepted §3.1 predicate. -/
def projectedWorld (s : State) (bytes : BackingRegionId → Finset AbstractByteId) : World where
  liveRegions := match s.current with | none => ∅ | some e => {region e}
  bytes := bytes
  access := fun _ => ⟨true,true⟩

theorem stable_world_is_disjoint (s : State) (bytes) : RegionsDisjoint (projectedWorld s bytes) := by
  intro a ha b hb ne
  cases h : s.current with
  | none => simp [projectedWorld,h] at ha
  | some e =>
    simp [projectedWorld,h] at ha hb
    exact False.elim (ne (ha.trans hb.symm))

/-- Existing kernel fact: two independently live overlapping byte-instance regions
cannot be an ordinary safe prestate, regardless of numeric addresses. -/
theorem aliasing_live_epochs_are_not_safe {w : World} {a b : BackingRegionId}
    (ha : a ∈ w.liveRegions) (hb : b ∈ w.liveRegions) (ne : a ≠ b)
    (overlap : ¬ Disjoint (w.bytes a) (w.bytes b)) : ¬ RegionsDisjoint w :=
  fun wf => overlap (wf a ha b hb ne)


/-- Three disjoint responsibilities, with header explicitly raw-owned. -/
def HeaderByte (b : Nat) : Prop := b < 32
def LivePrefixByte (n b : Nat) : Prop := 32 ≤ b ∧ b < 32 + 8*n
def VacantByte (e : Epoch) (n b : Nat) : Prop := 32 + 8*n ≤ b ∧ b < size e

theorem exact_header_live_vacant_partition (e : Epoch) (n b : Nat) (bound : n ≤ e.capacity) :
    b < size e ↔ HeaderByte b ∨ LivePrefixByte n b ∨ VacantByte e n b := by
  unfold HeaderByte LivePrefixByte VacantByte size
  omega

theorem no_header_live_overlap (n b) : ¬ (HeaderByte b ∧ LivePrefixByte n b) := by
  unfold HeaderByte LivePrefixByte; omega

theorem no_live_vacant_overlap (e n b) : ¬ (LivePrefixByte n b ∧ VacantByte e n b) := by
  unfold LivePrefixByte VacantByte; omega

theorem exact_responsibility_size (e : Epoch) (n : Nat) (bound : n ≤ e.capacity) :
    32 + 8*n + 8*(e.capacity-n) = size e := by unfold size; omega

theorem independent_element_ranges (i j b : Nat) (ne : i ≠ j) :
    ¬ (32+8*i ≤ b ∧ b < 32+8*(i+1) ∧ 32+8*j ≤ b ∧ b < 32+8*(j+1)) := by omega

def historicalIncarnations (s : State) : Finset IncarnationId :=
  s.used.biUnion (fun g => (Finset.range 16).image (fun i => (⟨32*g+i⟩ : IncarnationId)))

theorem new_incarnation_not_historically_allocated {s old r} (g : Grow s old r)
    (i : Nat) (hi : i < 16) : incarnation (nextEpoch old r) i ∉ historicalIncarnations s := by
  intro mem
  rcases Finset.mem_biUnion.mp mem with ⟨epoch,used,imem⟩
  rcases Finset.mem_image.mp imem with ⟨j,jmem,eq⟩
  have hj := Finset.mem_range.mp jmem
  have different : r.generation ≠ epoch := fun eq => g.fresh (eq ▸ used)
  have nums := congrArg IncarnationId.index eq
  simp only [incarnation,nextEpoch] at nums
  omega

theorem grow_requires_exact_ending_domain {s old r} (g : Grow s old r) :
    old.domain ∈ s.endingDomains := g.ending

/-- Accepted F1.5 relocation updates roots/claims within a FIXED backing world.
It cannot by itself prove a successful allocator epoch exchange. -/
theorem accepted_relocation_preserves_backing_world {g sites ctx s action receipt post}
    (raw : F1.Relocation.RawRelocate g sites ctx s action receipt post) :
    post.accounted.base.physical.world = s.accounted.base.physical.world := by
  cases raw with
  | same => rfl
  | move raw => rw [raw.post_eq]; rfl

theorem changed_world_is_not_an_accepted_relocation {g sites ctx s action receipt post}
    (changed : post.accounted.base.physical.world ≠ s.accounted.base.physical.world) :
    ¬ F1.Relocation.RawRelocate g sites ctx s action receipt post :=
  fun raw => changed (accepted_relocation_preserves_backing_world raw)

theorem same_place_cannot_change_current_state {g sites ctx s l id t e receipt post}
    (raw : F1.Relocation.RawRelocate g sites ctx s (.same l id t e) receipt post) : post = s :=
  (F1.Relocation.same_place_is_exact_identity raw).1


theorem take_all_transports_without_discard {s : State} (wf : WellFormed s) :
    WellFormed (takeAll s) := by
  constructor
  · cases h : s.current with
    | none =>
      have a := wf.active
      simp only [ActiveInvariant,h] at a
      simpa only [ActiveInvariant,takeAll,h] using (show s.ownerCredits = [] ∧ ([] : List Package) = [] ∧ (0 : Nat) = 0 ∧ s.cap = 0 from ⟨a.1,rfl,rfl,a.2.2.2⟩)
    | some e =>
      have a := wf.active
      simp only [ActiveInvariant,h] at a
      simpa only [ActiveInvariant,takeAll,h] using (show s.ownerCredits = [e.generation] ∧ Supported e.capacity ∧ (0 : Nat) = ([] : List Package).length ∧ s.cap = e.capacity ∧ ([] : List Package).length ≤ e.capacity ∧ e.generation ∈ s.used ∧ e.generation ∉ s.releases from ⟨a.1,a.2.1,rfl,a.2.2.2.1,Nat.zero_le _,a.2.2.2.2.2.1,a.2.2.2.2.2.2⟩)
  · simpa [takeAll] using wf.uniqueValues
  · exact wf.uniqueReleases
  · exact wf.recordedReleases

theorem free_preserves_wellFormed {s e} (f : Free s e) : WellFormed (freeCandidate s e) := by
  have a := f.1.active
  simp only [ActiveInvariant,f.2.1] at a
  constructor
  · exact ⟨rfl,f.2.2.1,by change s.len = 0; rw [a.2.2.1,f.2.2.1]; rfl,rfl⟩
  · exact f.1.uniqueValues
  · exact List.nodup_cons.mpr ⟨a.2.2.2.2.2.2,f.1.uniqueReleases⟩
  · intro x mem
    simp only [freeCandidate,List.mem_cons] at mem
    rcases mem with rfl|mem
    · exact a.2.2.2.2.2.1
    · exact f.1.recordedReleases _ mem

def FreeAt (s : State) (e : Epoch) (base : Nat) : Prop := Free s e ∧ base = e.address

theorem final_free_uses_current_header_base {s e base} (f : FreeAt s e base) :
    s.current = some e ∧ base = e.address := ⟨f.1.2.1,f.2⟩


/-- Accepted typed relocation preserves semantic package annotations; byte-copy
cannot replace this source/destination lifetime and claim transition. -/
theorem accepted_typed_move_keeps_package_data {g sites ctx s m receipt post}
    (raw : F1.Relocation.RawMove g sites ctx s m receipt post) :
    post.data = s.data ∧ post.accounted.base.semantic.values = s.accounted.base.semantic.values ∧
    (post.accounted.base.semantic.root m.destination).package =
      (s.accounted.base.semantic.root m.source).package := by
  rw [raw.post_eq]
  refine ⟨rfl,rfl,?_⟩
  simp [F1.Relocation.candidate,F1.Relocation.semanticCandidate,F1.Relocation.movedRoot,
    F1.Conditional.installRoot]

/-- An attempted prestate with an old live placement in an ended backing is
rejected by the accepted physical invariant, not just the experiment's checks. -/
theorem accepted_backing_requires_old_source_region {live p l pl}
    (wf : PhysicalWellFormed live p) (placed : p.placement l = some pl) :
    pl.region ∈ p.world.liveRegions := wf.regionLive l pl placed

end
end NewLang.Adjunct.ArrayEpoch
