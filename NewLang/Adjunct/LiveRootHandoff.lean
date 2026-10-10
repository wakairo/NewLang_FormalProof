import NewLang.Adjunct.Counterexample.BComposition
import NewLang.F0.Counterexample.Domain
import NewLang.F1.FixedLifetime
import Mathlib.Data.Multiset.Count

/-! Issue #47: NONCANONICAL finite whole-value projection. `Ticket` records
original identities, not an authority constructor in NewLang. The binding
operations below are proposed adapters, NOT accepted source evaluation rules.
No post-WF or unique-custody premise is used to prove their conservation.
Accepted heap predicates are used separately and the missing refinement remains
explicit. Lean records themselves are not affine language values. -/
namespace NewLang.Adjunct.LiveRootHandoff
open F0 FiveRoot
noncomputable section

abbrev Ticket := FiveRoot.Origin

structure Four where
  root : Ticket
  first : Ticket
  middle : Ticket
  last : Ticket
  deriving DecidableEq
structure Three where
  root : Ticket
  first : Ticket
  last : Ticket
  deriving DecidableEq
structure Two where
  root : Ticket
  child : Ticket
  deriving DecidableEq
structure Split where
  donor : Three
  detached : Ticket
  deriving DecidableEq

inductive Value where
  | ticket : Ticket → Value
  | four : Four → Value
  | three : Three → Value
  | two : Two → Value
  | split : Split → Value
  deriving DecidableEq

def Value.tickets : Value → Multiset Ticket
  | .ticket k => {k}
  | .four t => {t.root,t.first,t.middle,t.last}
  | .three t => {t.root,t.first,t.last}
  | .two t => {t.root,t.child}
  | .split t => {t.donor.root,t.donor.first,t.donor.last,t.detached}

inductive Binding where
  | donorA | receiverRoot | result | donor | detached | formalRoot | formalChild | treeB
  deriving DecidableEq
def bindings : List Binding := [.donorA,.receiverRoot,.result,.donor,.detached,
  .formalRoot,.formalChild,.treeB]
abbrev Frame := Binding → Option Value
def inventory (s : Frame) : Multiset Ticket :=
  (bindings.map fun b => ((s b).map Value.tickets).getD ∅).sum
def put (s : Frame) (b : Binding) (v : Option Value) : Frame :=
  fun q => if q = b then v else s q

def detachBody (t : Four) : Split := ⟨⟨t.root,t.first,t.last⟩,t.middle⟩
def detachPost (s : Frame) (t : Four) : Frame :=
  put (put s .donorA none) .result (some (.split (detachBody t)))
def openPost (s : Frame) (t : Split) : Frame :=
  put (put (put s .result none) .donor (some (.three t.donor)))
    .detached (some (.ticket t.detached))
def enterPost (s : Frame) (r k : Ticket) : Frame :=
  put (put (put (put s .receiverRoot none) .detached none)
    .formalRoot (some (.ticket r))) .formalChild (some (.ticket k))
def returnPost (s : Frame) (r k : Ticket) : Frame :=
  put (put (put s .formalRoot none) .formalChild none) .treeB (some (.two ⟨r,k⟩))

/-- These exact input/empty-output checks are finite affine transfer checks,
not an assertion that TreeTwo already owns the required result. -/
def Detach (s : Frame) (t : Four) : Prop := s .donorA = some (.four t) ∧ s .result = none
def Open (s : Frame) (t : Split) : Prop :=
  s .result = some (.split t) ∧ s .donor = none ∧ s .detached = none
def Enter (s : Frame) (r k : Ticket) : Prop :=
  s .receiverRoot = some (.ticket r) ∧ s .detached = some (.ticket k) ∧
  s .formalRoot = none ∧ s .formalChild = none
def Return (s : Frame) (r k : Ticket) : Prop :=
  s .formalRoot = some (.ticket r) ∧ s .formalChild = some (.ticket k) ∧ s .treeB = none

theorem detach_conserves {s t} (h : Detach s t) : inventory (detachPost s t) = inventory s := by
  apply Multiset.ext.mpr; intro k
  simp [inventory,bindings,detachPost,put,Value.tickets,detachBody,h.1,h.2,
    Multiset.count_cons,Multiset.count_add,Multiset.count_singleton,add_comm,add_left_comm,add_assoc]
theorem open_conserves {s t} (h : Open s t) : inventory (openPost s t) = inventory s := by
  apply Multiset.ext.mpr; intro k
  simp [inventory,bindings,openPost,put,Value.tickets,h.1,h.2.1,h.2.2,
    Multiset.count_cons,Multiset.count_add,Multiset.count_singleton,add_comm,add_left_comm,add_assoc]
theorem enter_conserves {s r k} (h : Enter s r k) : inventory (enterPost s r k) = inventory s := by
  apply Multiset.ext.mpr; intro x
  simp [inventory,bindings,enterPost,put,Value.tickets,h.1,h.2.1,h.2.2.1,h.2.2.2,
    Multiset.count_cons,Multiset.count_add,Multiset.count_singleton,add_comm,add_left_comm]
theorem return_conserves {s r k} (h : Return s r k) : inventory (returnPost s r k) = inventory s := by
  apply Multiset.ext.mpr; intro x
  simp [inventory,bindings,returnPost,put,Value.tickets,h.1,h.2.1,h.2.2,
    Multiset.count_cons,Multiset.count_add,Multiset.count_singleton,add_comm,add_left_comm]

theorem detach_consumes_donor (s : Frame) (t : Four) : detachPost s t .donorA = none := by
  simp [detachPost,put]
theorem enter_consumes_both (s : Frame) (r k : Ticket) :
    enterPost s r k .receiverRoot = none ∧ enterPost s r k .detached = none := by
  simp [enterPost,put]
theorem return_combines_exact_originals (s : Frame) (r k : Ticket) :
    returnPost s r k .treeB = some (.two ⟨r,k⟩) ∧
    returnPost s r k .formalRoot = none ∧ returnPost s r k .formalChild = none := by
  simp [returnPost,put]
theorem consumed_donor_rejects_detach (s : Frame) (t u : Four) : ¬ Detach (detachPost s t) u := by
  intro h; simpa [detachPost,put] using h.1
theorem consumed_holder_rejects_enter (s : Frame) (r k r' k' : Ticket) :
    ¬ Enter (enterPost s r k) r' k' := by
  intro h; simpa [enterPost,put] using h.1

/-- Match ALL original constituents; equal numeric pointer is insufficient.
This is checked against accepted origin/cell data, not nominal Ticket type. -/
def Matched (f : FiveRoot.State) (i : Site) (k : Ticket) : Prop :=
  k = f.origin i ∧ k.world = f.world ∧ Typed f i
theorem matched_wrong_world_rejected {f i k} (wrong : k.world ≠ f.world) : ¬ Matched f i k :=
  fun h => wrong h.2.1
theorem matched_wrong_region_rejected {f i k} (wrong : k.region ≠ (f.origin i).region) :
    ¬ Matched f i k := fun h => wrong (congrArg Origin.region h.1)
theorem matched_wrong_allocation_rejected {f i k} (wrong : k.allocation ≠ (f.origin i).allocation) :
    ¬ Matched f i k := fun h => wrong (congrArg Origin.allocation h.1)
theorem matched_wrong_domain_rejected {f i k} (wrong : k.domain ≠ (f.origin i).domain) :
    ¬ Matched f i k := fun h => wrong (congrArg Origin.domain h.1)

/-- Candidate local authority guard, explicitly MISSING ACCEPTED RICH ADAPTER.
It derives availability from a CURRENT binding's actual constituents, whereas
accepted FiveRoot.CanEnd by itself has no binding parameter. -/
def LocalCanEnd (f : FiveRoot.State) (s : Frame) (b : Binding) (i : Site) : Prop :=
  ∃ v k, s b = some v ∧ k ∈ v.tickets ∧ Matched f i k ∧ CanEnd f i k
theorem consumed_binding_cannot_end {f s b i} (consumed : s b = none) : ¬ LocalCanEnd f s b i := by
  rintro ⟨v,k,available,_,_,_⟩; rw [consumed] at available; cases available

/-- Accepted F0 only models identity-stability dependencies at this layer;
current domain-value borrowing is deliberately an explicit external premise. -/
theorem domainLive_alone_does_not_block_transfer :
    ∃ (s post : F0.State) (d : DomainId) (a b : DomainValueCarrierId)
      (p : PackageId) (v : ValuePackage),
      F0.WellFormed s ∧ F0.Survives s p ∧ s.packages p = some v ∧
      Fact.domainLive d ∈ v.dependencies ∧
      F0.DomainTransferStep True s d a b post ∧ a ≠ b := by
  have h := F0.Counterexample.Domain.DomainLive_dependency_allows_transfer_but_rejects_finalization
  exact ⟨_,_,_,_,_,_,_,h.1,h.2.1,rfl,h.2.2.1,h.2.2.2.1,by decide⟩

/-- A proper ordinary owner-place dependency DOES block consume-out, using
accepted F0 take semantics. Constructing this dependency from ticket@domain
and discharging transferAllowed is the unproved source/refinement interface. -/
theorem owner_place_loan_blocks_take {ce s post l root d p v}
    (wf : F0.WellFormed s) (_live : s.occupancy l = .live root)
    (survives : F0.Survives s p) (data : s.packages p = some v)
    (dep : Fact.valueFact root.place root.currentFact ∈ v.dependencies) :
    ¬ F0.TakeStep ce s l root d post :=
  F0.take_rejects_surviving_old_current_dependency wf survives data dep

/-- The rich fixed-subobject counterpart: a surviving capability depending on
the actual domain FIELD current fact blocks ending the whole enclosing owner.
The dependency must be generated by a separately proved loan adapter; the
field's DomainLive identity alone is insufficient. -/
theorem domain_field_loan_blocks_whole_consume {ce read s l d post p m q}
    (field : p ∈ (s.base.root l).layout.places) (owner : F1.LiveNode s.base m q)
    (other : m ≠ l)
    (dependency : Fact.valueFact p ((s.base.root l).node p).currentFact ∈
      F1.LocalDeps (s.base.root m) q) :
    ¬ F1.FixedLifetime.EndStep ce read s l d true post :=
  F1.FixedLifetime.end_rejects_external_ended_fact_dependency field owner other dependency

end
end NewLang.Adjunct.LiveRootHandoff
