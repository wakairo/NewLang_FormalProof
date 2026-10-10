import NewLang.Adjunct.OneBackingIssuerRich
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic

/-! Only ONE selected closed completed Node H. Layout is target supplied, not
an ABI theorem. Atomic Some/None is the trusted source-builtin contract;
intermediate carrier graphs document its member moves, not C execution. -/
namespace NewLang.Adjunct.OneBackingIssuerSource
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- The only H in this adjunct is the selected closed completed Node. -/
inductive ClosedH | node deriving DecidableEq
structure Target where
  h : ClosedH := .node
  sizeofH : Nat
  positive : 0 < sizeofH
  alignofH : Nat
  alignmentPositive : 0 < alignofH

inductive Carrier where
  | temporary : Nat → Carrier
  | allocationMember : Nat → Carrier
  | rawMember : Nat → Carrier
  | someMember : Nat → Carrier
  | result : Nat → Carrier
  deriving DecidableEq

/-- Nominal source lineage serial and value serials; neither is an address. -/
structure Grant where
  region : Nat
  origin : Nat
  base : Nat
  n : Nat
  observedAddress : Nat
  deriving DecidableEq

def Grant.edges (p : Grant) : Finset (Nat × Carrier) :=
  {(p.base,.allocationMember (p.base+2)),(p.base+1,.rawMember (p.base+2)),
   (p.base+2,.someMember (p.base+3)),(p.base+3,.result (p.base+3))}

/-- Initial a/raw temporary bindings are replaced by member placements. -/
def Grant.temporaryEdges (p : Grant) : Finset (Nat × Carrier) :=
  {(p.base,.temporary p.base),(p.base+1,.temporary (p.base+1))}

def Grant.packedEdges (p : Grant) : Finset (Nat × Carrier) :=
  {(p.base,.allocationMember (p.base+2)),(p.base+1,.rawMember (p.base+2)),
   (p.base+2,.temporary (p.base+2))}

/-- Actual placement moves: remove the two temporary bindings and create the
same a/raw member bindings plus the ordinary aggregate wrapper. -/
def pack (p : Grant) (edges : Finset (Nat × Carrier)) : Finset (Nat × Carrier) :=
  ((edges.erase (p.base,.temporary p.base)).erase (p.base+1,.temporary (p.base+1))) ∪
    {(p.base,.allocationMember (p.base+2)),(p.base+1,.rawMember (p.base+2)),
      (p.base+2,.temporary (p.base+2))}

def wrap (p : Grant) (edges : Finset (Nat × Carrier)) : Finset (Nat × Carrier) :=
  edges.erase (p.base+2,.temporary (p.base+2)) ∪
    {(p.base+2,.someMember (p.base+3)),(p.base+3,.result (p.base+3))}

theorem pack_temporaries (p : Grant) : pack p p.temporaryEdges = p.packedEdges := by
  simp [pack,Grant.temporaryEdges,Grant.packedEdges]

theorem wrap_packed (p : Grant) : wrap p p.packedEdges = p.edges := by
  simp [wrap,Grant.packedEdges,Grant.edges,Finset.erase_insert_of_ne,Finset.insert_comm]

def Unique (edges : Finset (Nat × Carrier)) : Prop :=
  ∀ v c d, (v,c) ∈ edges → (v,d) ∈ edges → c = d

inductive Extra | typedRoot | domain | pointer | loan | incarnation deriving DecidableEq
structure Source where
  nextRegion : Nat
  nextValue : Nat
  grants : Finset Grant
  current : Finset (Nat × Carrier)
  consumed : Finset Nat
  extras : Finset Extra

structure SourceWF (s : Source) : Prop where
  regionBelow : ∀ p ∈ s.grants, p.region < s.nextRegion
  regionUnique : ∀ p ∈ s.grants, ∀ q ∈ s.grants, p.region = q.region → p = q
  valueBelow : ∀ p ∈ s.grants, p.base+4 ≤ s.nextValue
  origin : ∀ p ∈ s.grants, p.origin = p.region
  positive : ∀ p ∈ s.grants, 0 < p.n
  currentExact : s.current = s.grants.biUnion Grant.edges
  unique : Unique s.current
  noEarly : s.extras = ∅

/-- Allocator returns only status and aligned address observation. Resource
freshness/disjoint abstract bytes are a separate Supply, not an Allocation. -/
structure Success (t : Target) where
  address : Nat
  aligned : address % t.alignofH = 0

def freshGrant (t : Target) (s : Source) (ok : Success t) : Grant :=
  ⟨s.nextRegion,s.nextRegion,s.nextValue,t.sizeofH,ok.address⟩

def somePost (t : Target) (s : Source) (ok : Success t) : Source where
  nextRegion := s.nextRegion+1
  nextValue := s.nextValue+4
  grants := insert (freshGrant t s ok) s.grants
  current := (freshGrant t s ok).edges ∪ s.current
  consumed := {s.nextValue,s.nextValue+1,s.nextValue+2} ∪ s.consumed
  extras := s.extras

inductive Outcome | none | some (resultValue : Nat) deriving DecidableEq

/-- The trusted atomic source primitive. No new A/raw/Some/R occurs in PRE.
None includes the platform's INTERNAL refund guarantee by exposing identity. -/
inductive Step (t : Target) : Source → Outcome → Source → Prop where
  | some (s : Source) (oldWF : SourceWF s) (bounded : s.grants.card ≤ 1)
      (ok : Success t) : Step t s (.some (s.nextValue+3)) (somePost t s ok)
  | none (s : Source) (oldWF : SourceWF s) (bounded : s.grants.card ≤ 1) :
      Step t s .none s

theorem edges_bounds (p : Grant) {v c} (edge : (v,c) ∈ p.edges) :
    p.base ≤ v ∧ v < p.base+4 := by
  simp [Grant.edges] at edge
  rcases edge with edge | edge | edge | edge <;> rcases edge with ⟨rfl,_⟩ <;> omega

theorem edges_unique (p : Grant) : Unique p.edges := by
  intro v c d hc hd
  simp [Grant.edges] at hc hd
  rcases hc with hc | hc | hc | hc <;> rcases hd with hd | hd | hd | hd <;>
    rcases hc with ⟨hv,hc⟩ <;> rcases hd with ⟨hw,hd⟩ <;> simp_all

theorem old_current_below {s} (wf : SourceWF s) {v c} (edge : (v,c) ∈ s.current) :
    v < s.nextValue := by
  rw [wf.currentExact] at edge
  rcases Finset.mem_biUnion.mp edge with ⟨p,member,edge⟩
  have := edges_bounds p edge
  have := wf.valueBelow p member
  omega

theorem some_source_wellFormed {t s} (wf : SourceWF s) (ok : Success t) :
    SourceWF (somePost t s ok) := by
  constructor
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [freshGrant,somePost]
    · have := wf.regionBelow p member; simp only [somePost]; omega
  · intro p pm q qm eq
    simp only [somePost,Finset.mem_insert] at pm qm
    rcases pm with rfl | pm <;> rcases qm with rfl | qm
    · rfl
    · have := wf.regionBelow q qm
      simp only [freshGrant] at eq; omega
    · have := wf.regionBelow p pm
      simp only [freshGrant] at eq; omega
    · exact wf.regionUnique p pm q qm eq
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [freshGrant,somePost]
    · have := wf.valueBelow p member; simp only [somePost]; omega
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · rfl
    · exact wf.origin p member
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · exact t.positive
    · exact wf.positive p member
  · simp [somePost,Finset.biUnion_insert,← wf.currentExact]
  · intro v c d hc hd
    simp only [somePost,Finset.mem_union] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd
    · exact edges_unique _ v c d hc hd
    · have lo := (edges_bounds _ hc).1
      have hi := old_current_below wf hd
      simp only [freshGrant] at lo; omega
    · have lo := (edges_bounds _ hd).1
      have hi := old_current_below wf hc
      simp only [freshGrant] at lo; omega
    · exact wf.unique v c d hc hd
  · exact wf.noEarly

theorem old_grant_not_fresh {t s} (wf : SourceWF s) (ok : Success t) :
    freshGrant t s ok ∉ s.grants := by
  intro member
  have := wf.regionBelow _ member
  simp [freshGrant] at this

theorem some_is_bounded {t s} (wf : SourceWF s) (bounded : s.grants.card ≤ 1)
    (ok : Success t) : (somePost t s ok).grants.card ≤ 2 := by
  simp only [somePost,Finset.card_insert_of_notMem (old_grant_not_fresh wf ok)]
  omega

theorem moves_consume_temporaries (p : Grant) :
    (p.base,.temporary p.base) ∈ p.temporaryEdges ∧
    (p.base+1,.temporary (p.base+1)) ∈ p.temporaryEdges ∧
    (p.base+2,.temporary (p.base+2)) ∈ p.packedEdges ∧
    (∀ v k, (v,.temporary k) ∉ p.edges) ∧
    (p.base,.allocationMember (p.base+2)) ∈ p.packedEdges ∧
    (p.base+1,.rawMember (p.base+2)) ∈ p.packedEdges ∧
    (p.base,.allocationMember (p.base+2)) ∈ p.edges ∧
    (p.base+1,.rawMember (p.base+2)) ∈ p.edges := by
  simp [Grant.temporaryEdges,Grant.packedEdges,Grant.edges]

theorem some_event_has_actual_move_trace {t s} (ok : Success t) :
    (somePost t s ok).current =
      wrap (freshGrant t s ok) (pack (freshGrant t s ok) (freshGrant t s ok).temporaryEdges) ∪ s.current ∧
    {s.nextValue,s.nextValue+1,s.nextValue+2} ⊆ (somePost t s ok).consumed := by
  rw [pack_temporaries,wrap_packed]
  exact ⟨rfl,Finset.subset_union_left⟩

theorem exactly_one_new_result (p : Grant) :
    (∀ v k, (v,.result k) ∈ p.edges ↔ v = p.base+3 ∧ k = p.base+3) ∧
    (p.base+2,.someMember (p.base+3)) ∈ p.edges := by
  simp [Grant.edges]

theorem some_old_current_frame {t s} (_wf : SourceWF s) (ok : Success t) {v c}
    (old : v < s.nextValue) :
    (v,c) ∈ (somePost t s ok).current ↔ (v,c) ∈ s.current := by
  simp only [somePost,Finset.mem_union]
  constructor
  · rintro (new | oldEdge)
    · have := (edges_bounds _ new).1
      simp [freshGrant] at this; omega
    · exact oldEdge
  · exact Or.inr

theorem new_allocation_has_exactly_one_current_carrier {t s} (wf : SourceWF s)
    (ok : Success t) (c : Carrier) :
    (s.nextValue,c) ∈ (somePost t s ok).current ↔ c = .allocationMember (s.nextValue+2) := by
  have present : (s.nextValue,.allocationMember (s.nextValue+2)) ∈ (somePost t s ok).current := by
    apply Finset.mem_union_left
    simp [freshGrant,Grant.edges]
  constructor
  · intro edge; exact (some_source_wellFormed wf ok).unique _ _ _ edge present
  · intro eq; subst c; exact present

theorem none_identity {t s post} (step : Step t s .none post) : post = s := by
  cases step; rfl

/-- Interpretation is independent data. Nominal lineage, opaque ORIGINAL A
value, raw value's ghost claim, and retired rich region history stay distinct. -/
structure Interpretation where
  region : Nat → BackingRegionId
  allocation : Nat → Option BackingRegionId
  rawClaim : Nat → ClaimId
  usedRegions : Finset BackingRegionId

/-- A generic inventory/current-ownership interpretation, not post equality or
an allocator-success predicate. Rich WF is deliberately a separate obligation. -/
structure Refines (src : Source) (g : Geometry) (rich : F1.Occupancy.State)
    (i : Interpretation) : Prop where
  regionHistory : ∀ r < src.nextRegion, i.region r ∈ i.usedRegions
  lineageUnique : ∀ r < src.nextRegion, ∀ q < src.nextRegion,
    i.region r = i.region q → r = q
  allocationInventory : ∀ v, (∃ r, i.allocation v = some r) ↔ ∃ p ∈ src.grants, p.base = v
  allocationOrigin : ∀ p ∈ src.grants, i.allocation p.base = some (i.region p.origin)
  fullRaw : ∀ p ∈ src.grants,
    Has rich.ledger (i.rawClaim (p.base+1)) (.storage ⟨i.region p.region,⟨0,p.n⟩⟩)
  exactCapacity : ∀ p ∈ src.grants, g.capacity (i.region p.region) = p.n
  regionInventory : rich.flat.physical.world.liveRegions = src.grants.image (fun p => i.region p.region)
  scopeInventory : rich.ledger.scope = src.grants.image (fun p => i.region p.region)
  claimInventory : rich.ledger.active = src.grants.image (fun p => i.rawClaim (p.base+1))
  semanticEmpty : rich.flat.semantic = F0.State.empty
  placementEmpty : rich.flat.physical.placement = fun _ => none
  currentOwnership : src.current = src.grants.biUnion Grant.edges

/-- Construct the interpretation from fresh resource names and GENERATED
source serials. There is no interpretation of a new original A in PRE. -/
def interpretationPost {g rich} (a : OneBackingIssuerRich.Supply g rich) (src : Source)
    (i : Interpretation) : Interpretation where
  region r := if r = src.nextRegion then a.region else i.region r
  allocation v := if v = src.nextValue then some a.region else i.allocation v
  rawClaim v := if v = src.nextValue+1 then a.claim else i.rawClaim v
  usedRegions := insert a.region i.usedRegions

theorem interpretation_old_frame {g rich} (a : OneBackingIssuerRich.Supply g rich) {src i}
    (wf : SourceWF src) {p} (member : p ∈ src.grants) :
    (interpretationPost a src i).region p.region = i.region p.region ∧
    (interpretationPost a src i).region p.origin = i.region p.origin ∧
    (interpretationPost a src i).allocation p.base = i.allocation p.base ∧
    (interpretationPost a src i).rawClaim (p.base+1) = i.rawClaim (p.base+1) := by
  have rb := wf.regionBelow p member
  have vb := wf.valueBelow p member
  have origin := wf.origin p member
  have rn : p.region ≠ src.nextRegion := by omega
  have on : p.origin ≠ src.nextRegion := by omega
  have an : p.base ≠ src.nextValue := by omega
  simp [interpretationPost,rn,on,an]

theorem refines_old_live {src g rich i} (ref : Refines src g rich i) {p}
    (member : p ∈ src.grants) : i.region p.region ∈ rich.flat.physical.world.liveRegions := by
  rw [ref.regionInventory]
  exact Finset.mem_image.mpr ⟨p,member,rfl⟩

/-- The first actual simulation: fresh source serials and member moves issue
A/raw/Some, while the adjunct rich constructor INTRODUCES backing and scope. -/
theorem some_post_refines {t src g layout rich i}
    (swf : SourceWF src) (rwf : WellFormed g layout rich)
    (ref : Refines src g rich i) (ok : Success t) (a : OneBackingIssuerRich.Supply g rich)
    (size : a.n = t.sizeofH) (freshHistory : a.region ∉ i.usedRegions) :
    Refines (somePost t src ok) (OneBackingIssuerRich.geometry a) (OneBackingIssuerRich.post a)
      (interpretationPost a src i) := by
  have frame := fun {p} (member : p ∈ src.grants) => interpretation_old_frame (i := i) a swf member
  have oldRegions : src.grants.image (fun p => (interpretationPost a src i).region p.region) =
      src.grants.image (fun p => i.region p.region) :=
    Finset.image_congr (fun p member => (frame member).1)
  have oldClaims : src.grants.image (fun p => (interpretationPost a src i).rawClaim (p.base+1)) =
      src.grants.image (fun p => i.rawClaim (p.base+1)) :=
    Finset.image_congr (fun p member => (frame member).2.2.2)
  constructor
  · intro r below
    by_cases eq : r = src.nextRegion
    · simp [interpretationPost,eq]
    · have old : r < src.nextRegion := by simp only [somePost] at below; omega
      simpa [interpretationPost,eq] using Finset.mem_insert_of_mem (ref.regionHistory r old)
  · intro r rb q qb eq
    by_cases re : r = src.nextRegion <;> by_cases qe : q = src.nextRegion
    · exact re.trans qe.symm
    · have old : q < src.nextRegion := by simp only [somePost] at qb; omega
      have same : a.region = i.region q := by simpa [interpretationPost,re,qe] using eq
      exact False.elim (freshHistory (same ▸ ref.regionHistory q old))
    · have old : r < src.nextRegion := by simp only [somePost] at rb; omega
      have same : i.region r = a.region := by simpa [interpretationPost,re,qe] using eq
      exact False.elim (freshHistory (same ▸ ref.regionHistory r old))
    · have rold : r < src.nextRegion := by simp only [somePost] at rb; omega
      have qold : q < src.nextRegion := by simp only [somePost] at qb; omega
      exact ref.lineageUnique r rold q qold (by simpa [interpretationPost,re,qe] using eq)
  · intro v
    by_cases eq : v = src.nextValue
    · subst v
      constructor
      · intro _; exact ⟨freshGrant t src ok,Finset.mem_insert_self _ _,rfl⟩
      · intro _; exact ⟨a.region,by simp [interpretationPost]⟩
    · simp only [interpretationPost,eq,ite_false]
      rw [ref.allocationInventory]
      constructor
      · rintro ⟨p,member,base⟩; exact ⟨p,Finset.mem_insert_of_mem member,base⟩
      · rintro ⟨p,member,base⟩
        simp only [somePost,Finset.mem_insert] at member
        rcases member with rfl | member
        · exact False.elim (eq base.symm)
        · exact ⟨p,member,base⟩
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [freshGrant,interpretationPost]
    · rw [(frame member).2.2.1,(frame member).2.1]
      exact ref.allocationOrigin p member
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simpa [freshGrant,interpretationPost,OneBackingIssuerRich.extent,size] using OneBackingIssuerRich.full_has a
    · rw [(frame member).2.2.2,(frame member).1]
      have has := ref.fullRaw p member
      exact ⟨Finset.mem_insert_of_mem has.1,(OneBackingIssuerRich.old_claim_frame a has.1).trans has.2⟩
  · intro p member
    simp only [somePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [freshGrant,interpretationPost,OneBackingIssuerRich.geometry,size]
    · rw [(frame member).1,(OneBackingIssuerRich.old_world_frame rwf a (refines_old_live ref member)).2.2.1]
      exact ref.exactCapacity p member
  · simp only [OneBackingIssuerRich.post,OneBackingIssuerRich.world,somePost,Finset.image_insert]
    simp only [freshGrant,interpretationPost,ite_true]
    rw [show src.grants.image (fun p => if p.region = src.nextRegion then a.region else i.region p.region) = _ from oldRegions]
    exact congrArg (insert a.region) ref.regionInventory
  · change insert a.region rich.ledger.scope = _
    simp only [somePost,Finset.image_insert,freshGrant,interpretationPost,ite_true]
    rw [show src.grants.image (fun p => if p.region = src.nextRegion then a.region else i.region p.region) = _ from oldRegions]
    exact congrArg (insert a.region) ref.scopeInventory
  · change insert a.claim rich.ledger.active = _
    simp only [somePost,Finset.image_insert,freshGrant,interpretationPost,ite_true]
    rw [show src.grants.image (fun p => if p.base+1 = src.nextValue+1 then a.claim else i.rawClaim (p.base+1)) = _ from oldClaims]
    exact congrArg (insert a.claim) ref.claimInventory
  · exact ref.semanticEmpty
  · exact ref.placementEmpty
  · exact (some_source_wellFormed swf ok).currentExact

theorem some_simulation {t src g layout rich i}
    (swf : SourceWF src) (bounded : src.grants.card ≤ 1)
    (rwf : WellFormed g layout rich) (ref : Refines src g rich i)
    (ok : Success t) (a : OneBackingIssuerRich.Supply g rich) (size : a.n = t.sizeofH)
    (freshHistory : a.region ∉ i.usedRegions) :
    Step t src (.some (src.nextValue+3)) (somePost t src ok) ∧
    SourceWF (somePost t src ok) ∧
    Refines (somePost t src ok) (OneBackingIssuerRich.geometry a) (OneBackingIssuerRich.post a) (interpretationPost a src i) ∧
    WellFormed (OneBackingIssuerRich.geometry a) layout (OneBackingIssuerRich.post a) :=
  ⟨Step.some src swf bounded ok,some_source_wellFormed swf ok,
    some_post_refines swf rwf ref ok a size freshHistory,OneBackingIssuerRich.constructive_wellFormed rwf a⟩

theorem none_simulation {t src g layout rich i}
    (swf : SourceWF src) (bounded : src.grants.card ≤ 1)
    (rwf : WellFormed g layout rich) (ref : Refines src g rich i) :
    Step t src .none src ∧ SourceWF src ∧ Refines src g rich i ∧ WellFormed g layout rich :=
  ⟨Step.none src swf bounded,swf,ref,rwf⟩

/-- Joint interpreter event. The only None constructor keeps ALL four views;
Some takes resource input and constructs each view, with no post premise. -/
inductive IssuerEvent (t : Target) (src : Source) (g : Geometry)
    (rich : F1.Occupancy.State) (i : Interpretation) :
    Outcome → Source → Geometry → F1.Occupancy.State → Interpretation → Prop where
  | some (swf : SourceWF src) (bounded : src.grants.card ≤ 1)
      (ok : Success t) (a : OneBackingIssuerRich.Supply g rich)
      (size : a.n = t.sizeofH) (freshHistory : a.region ∉ i.usedRegions) :
      IssuerEvent t src g rich i (.some (src.nextValue+3)) (somePost t src ok)
        (OneBackingIssuerRich.geometry a) (OneBackingIssuerRich.post a) (interpretationPost a src i)
  | none (swf : SourceWF src) (bounded : src.grants.card ≤ 1) :
      IssuerEvent t src g rich i .none src g rich i

theorem every_issuer_event_refines {t src g layout rich i outcome src' g' rich' i'}
    (rwf : WellFormed g layout rich) (ref : Refines src g rich i)
    (event : IssuerEvent t src g rich i outcome src' g' rich' i') :
    Step t src outcome src' ∧ SourceWF src' ∧ Refines src' g' rich' i' ∧
      WellFormed g' layout rich' := by
  cases event with
  | some swf bounded ok a size fresh => exact some_simulation swf bounded rwf ref ok a size fresh
  | none swf bounded => exact none_simulation swf bounded rwf ref

theorem every_none_event_is_full_identity {t src g rich i src' g' rich' i'}
    (event : IssuerEvent t src g rich i .none src' g' rich' i') :
    src' = src ∧ g' = g ∧ rich' = rich ∧ i' = i := by
  cases event; exact ⟨rfl,rfl,rfl,rfl⟩

/-- Opaque original-A identity uniqueness is a SOURCE inventory/current value
law plus lineage interpretation, independently of rich byte accounting. -/
theorem pre_has_no_future_allocation_or_carrier {src g rich i}
    (swf : SourceWF src) (ref : Refines src g rich i) :
    i.allocation src.nextValue = none ∧ ∀ c, (src.nextValue,c) ∉ src.current := by
  constructor
  · cases eq : i.allocation src.nextValue with
    | none => rfl
    | some r =>
      rcases (ref.allocationInventory src.nextValue).mp ⟨r,eq⟩ with ⟨p,member,base⟩
      have := swf.valueBelow p member
      omega
  · intro c edge
    have := old_current_below swf edge
    omega

theorem one_original_allocation_per_R {src g rich i}
    (swf : SourceWF src) (ref : Refines src g rich i) {p q}
    (pm : p ∈ src.grants) (qm : q ∈ src.grants)
    (sameR : i.region p.origin = i.region q.origin) : p = q := by
  rw [swf.origin p pm,swf.origin q qm] at sameR
  exact swf.regionUnique p pm q qm
    (ref.lineageUnique p.region (swf.regionBelow p pm) q.region (swf.regionBelow q qm) sameR)

theorem success_has_no_early_authority {t src g rich i}
    (swf : SourceWF src) (ref : Refines src g rich i) (ok : Success t)
    (a : OneBackingIssuerRich.Supply g rich) :
    (somePost t src ok).extras = ∅ ∧
    (OneBackingIssuerRich.post a).flat.semantic = F0.State.empty ∧
    (OneBackingIssuerRich.post a).flat.physical.placement = fun _ => none :=
  ⟨swf.noEarly,ref.semanticEmpty,ref.placementEmpty⟩

end
end NewLang.Adjunct.OneBackingIssuerSource
