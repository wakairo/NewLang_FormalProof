import NewLang.Adjunct.FreshDomainWitness
import NewLang.F2.Model

namespace NewLang.Adjunct.FreshDomainCounterexample
open F0 F1.Backing F1.Occupancy OneBackingSlotSource OneBackingSlotRich FreshDomainRich
open FreshDomainWitness OneBackingSlotWitness
noncomputable section

/-- Actual duplicate Domain value: same D, second available nonCopy value. -/
def duplicateD : FreshDomainSource.State :=
  {after with available := insert (domain,value+1) after.available}
theorem duplicate_D_value_rejected_while_rich_wf :
    ¬ FreshDomainSource.SourceWF context duplicateD ∧
    WellFormed OneBackingIssuerWitness.afterGeometry typing.layout domainRich := by
  refine ⟨?_,complete_issue.2.2⟩
  intro wf
  have a : (domain,value) ∈ FreshDomainSource.current duplicateD := by
    simp [FreshDomainSource.current,duplicateD,after,FreshDomainSource.issuePost,before,FreshDomainSource.start,domain,value]
  have b : (domain,value+1) ∈ FreshDomainSource.current duplicateD := by simp [FreshDomainSource.current,duplicateD]
  have equal := wf.domainUnique domain value (value+1) a b
  omega

def copiedPlacement : FreshDomainSource.State := {after with outgoing := {(domain,value)}}
theorem copied_current_placement_rejected : ¬ FreshDomainSource.SourceWF context copiedPlacement := by
  intro wf
  exact Finset.disjoint_left.mp wf.distinctPlaces
    (by simp [copiedPlacement,after,FreshDomainSource.issuePost,before,FreshDomainSource.start,domain,value])
    (Finset.mem_singleton_self _)

def clonedIdentity : FreshDomainSource.State :=
  {after with available := insert (⟨2⟩,value) after.available}
theorem cloned_domain_from_same_value_rejected : ¬ FreshDomainSource.SourceWF context clonedIdentity := by
  intro wf
  have old : (domain,value) ∈ FreshDomainSource.current clonedIdentity := by
    simp [FreshDomainSource.current,clonedIdentity,after,FreshDomainSource.issuePost,before,FreshDomainSource.start,domain,value]
  have new : (⟨2⟩,value) ∈ FreshDomainSource.current clonedIdentity := by simp [FreshDomainSource.current,clonedIdentity]
  have equal : (⟨2⟩ : DomainId) = ⟨1⟩ := wf.valueUnique _ _ _ new old
  cases equal

/-- Old D=0 is retired history. Matching R_C's NUMBER is not Domain issuance. -/
theorem retired_D_cannot_be_issued_by_selected_event :
    (⟨0⟩ : DomainId) ∈ before.usedDomains ∧
    (⟨0⟩ : DomainId) ≠ FreshDomainSource.newDomain before ∧
    domain ∈ after.usedDomains ∧ domain ≠ FreshDomainSource.newDomain after := by
  refine ⟨by decide,by decide,?_,by decide⟩
  simp [after,FreshDomainSource.issuePost,domain]

theorem no_second_issue_in_this_one_call_slice (post : FreshDomainSource.State) :
    ¬ FreshDomainSource.Issue context after post := by
  intro second; cases second.phase

/-- Ordinary affine move-to-result is modeled solely to audit exactly-once
consumption/normal-exit; no finalize/loan/typed object transition is added. -/
def forwarded := FreshDomainSource.forwardPost after domain value
theorem normal_domain_forwarding :
    FreshDomainSource.Forward context after domain value forwarded ∧
    FreshDomainSource.SourceWF context forwarded ∧
    FreshDomainSource.current forwarded = FreshDomainSource.current after ∧
    RefinesDomain context forwarded OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot domainRich OneBackingIssuerWitness.afterInterpretation typing slotHandle := by
  have available : (domain,value) ∈ after.available := by
    simp [after,FreshDomainSource.issuePost,before,FreshDomainSource.start,domain,value]
  exact ⟨⟨complete_issue.2.1.source,available,rfl⟩,
    FreshDomainSource.forward_wellFormed complete_issue.2.1.source available,
    FreshDomainSource.forward_current available,forward_refines complete_issue.2.1 available⟩

theorem double_consume_rejected (post : FreshDomainSource.State) :
    ¬ FreshDomainSource.Forward context forwarded domain value post :=
  FreshDomainSource.forward_cannot_consume_twice normal_domain_forwarding.1 post

theorem nonDiscardable_normal_exit_obligation (ownerResult : Custody) :
    ¬ FreshDomainSource.NormalExit after ownerResult ∅ := by
  intro exit
  have present : (domain,value) ∈ FreshDomainSource.current after := by
    simp [FreshDomainSource.current,after,FreshDomainSource.issuePost,before,FreshDomainSource.start,domain,value]
  rw [← exit.domains] at present; simp at present

def lostSlotOwners : Custody := {slotSource with current := slotSource.current.erase (1008,.slotLocal)}
def lostSlot : FreshDomainSource.State := {after with owners := lostSlotOwners}
theorem lost_empty_slot_rejected : ¬ FreshDomainSource.SourceWF context lostSlot := by
  intro wf
  have present : (1008,Binding.slotLocal) ∈ lostSlotOwners.current := by
    change (1008,Binding.slotLocal) ∈ lostSlot.owners.current
    rw [wf.owners.currentExact,wf.slot]
    simp [packetGraph,context,Context.packet,OneBackingIssuerSource.freshGrant,OneBackingIssuerWitness.beforeSource]
  simp [lostSlotOwners] at present

def lostAOwners : Custody := {slotSource with allocation := none}
def lostA : FreshDomainSource.State := {after with owners := lostAOwners}
theorem lost_original_A_rejected : ¬ FreshDomainSource.SourceWF context lostA := by
  intro wf
  have equal : (none : Option Nat) = some 1004 := wf.owners.allocation
  cases equal

def earlyTyped : FreshDomainSource.State := {after with extras := {.typedRoot,.pointer,.incarnation}}
theorem invented_typed_root_ptr_incarnation_rejected : ¬ FreshDomainSource.SourceWF context earlyTyped := by
  intro wf
  have nonempty : FreshDomainSource.Extra.typedRoot ∈ earlyTyped.extras := by simp [earlyTyped]
  rw [wf.noEarly] at nonempty; simp at nonempty

/-- Guessing even the NEXT actual Domain ID through a copied persistent token
provides no current authority before the real source event. -/
theorem copied_pointer_cannot_guess_domain_authority (p : PtrToken) :
    ¬ (∃ v, (domain,v) ∈ FreshDomainSource.current before) ∧
    ¬ AcquireRef True True domainRich.flat.semantic p domain :=
  ⟨by simp [FreshDomainSource.current,before,FreshDomainSource.start],
    (lexical_domain_loan_first_bridge_unproved True True p).2.2⟩

/-- An UNVALIDATED outside assertion of a loan is not an accepted ref. Its
projection is just the real live D/carrier state. Core True permission still
admits movement: the actual scope permission is a missing interface. -/
structure UnvalidatedLoan where
  domain : DomainId
  scopeSerial : Nat

def claimedLoan : UnvalidatedLoan := ⟨domain,37⟩
theorem projected_domain_state_does_not_supply_loan_transfer_guard :
    claimedLoan.domain = domain ∧
    F0.DomainTransferStep True domainRich.flat.semantic domain ⟨value⟩ ⟨1010⟩
      (F0.domainTransferCandidate domainRich.flat.semantic domain ⟨1010⟩) := by
  refine ⟨rfl,F0.domain_transfer_step_of_raw complete_issue.2.2.toWellFormed ?_⟩
  exact ⟨(lexical_domain_loan_first_bridge_unproved True True ⟨⟨0⟩,⟨0⟩⟩).1,
    actual_fresh_D_available.2.2.2.2.2.2.2.2.2.1,trivial,rfl⟩

/-- Again this is a negative projection control, NOT a valid loan/finalization
trace. Scope-sensitive canFinalize cannot be replaced by current D liveness. -/
theorem projected_domain_state_does_not_supply_loan_finalize_guard :
    claimedLoan.domain = domain ∧
    F0.RawFinalizeDomain True domainRich.flat.semantic domain ⟨value⟩
      (F0.finalizeDomainCandidate domainRich.flat.semantic domain) ∧
    F0.WellFormed (F0.finalizeDomainCandidate domainRich.flat.semantic domain) := by
  refine ⟨rfl,⟨(lexical_domain_loan_first_bridge_unproved True True ⟨⟨0⟩,⟨0⟩⟩).1,
    actual_fresh_D_available.2.2.2.2.2.2.2.2.2.1,trivial,rfl⟩,?_⟩
  -- Domain-only semantic state ends back at empty; no object lifetime is ended.
  have same : F0.finalizeDomainCandidate domainRich.flat.semantic domain = F0.State.empty := by
    have carrier : (fun q : DomainId => if q = domain then (none : Option DomainValueCarrierId)
        else if q = domain then some ⟨value⟩ else none) = (fun _ => none) := by
      funext q; by_cases eq : q = domain <;> simp [eq]
    change {F0.State.empty with
      liveDomains := ({domain} : Finset DomainId).erase domain
      domainValueCarrier := fun q => if q = domain then none else if q = domain then some ⟨value⟩ else none} = F0.State.empty
    rw [Finset.erase_singleton,carrier]
    rfl

  rw [same]; exact F0.empty_wellFormed

/-- F2 rejects a REGISTERED ending-scope dependency, but no accepted operation
registers a Domain-value lexical ref under such a binding in this entry. -/
theorem escaped_registered_scope_dependency_rejected (scope : F2.BindingId) :
    ¬ F2.ScopeClosed ({F2.Dependency.iteration scope} : Finset F2.Dependency) := by
  intro closed; exact closed scope (Finset.mem_singleton_self _)

/-- Repeating the old issuer None arm preserves ALL views; lifetime_domain()
itself is not fallible and is not assigned a fictitious None arm. -/
theorem repeated_none_is_identity {target old g rich i mid gm rm im final gf rf ifinal}
    (first : OneBackingIssuerSource.IssuerEvent target old g rich i .none mid gm rm im)
    (second : OneBackingIssuerSource.IssuerEvent target mid gm rm im .none final gf rf ifinal) :
    final = old ∧ gf = g ∧ rf = rich ∧ ifinal = i := by
  have a := OneBackingIssuerSource.every_none_event_is_full_identity first
  have b := OneBackingIssuerSource.every_none_event_is_full_identity second
  exact ⟨b.1.trans a.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,b.2.2.2.trans a.2.2.2⟩

theorem concrete_none_has_no_slot_domain_successor :
    (∀ s, ¬ FreshDomainSource.Entrance context .none s) ∧
    OneBackingIssuerWitness.beforeRich.flat.semantic.liveDomains = ∅ ∧
    OneBackingIssuerWitness.beforeInterpretation.allocation 1004 = none :=
  ⟨FreshDomainSource.none_has_no_domain_successor context,rfl,rfl⟩

/-- Merely placing a live D into rich PRE cannot replace the real source issue. -/
theorem fabricated_pre_domain_refinement_rejected :
    ¬ RefinesDomain context before OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot domainRich OneBackingIssuerWitness.afterInterpretation typing slotHandle := by
  intro ref
  have h : ({domain} : Finset DomainId) = ∅ := ref.domains
  have member := Finset.mem_singleton_self domain
  rw [h] at member; simp at member

/-- DomainLive alone cannot encode a loan's ending lexical binding. The F2
escape check only rejects once the actual scope dependency is registered. -/
theorem domainLive_dependency_is_not_lexical_scope_protection :
    F2.ScopeClosed ({F2.Dependency.externalFact (.domainLive domain)} : Finset F2.Dependency) := by
  intro b; simp

def forgedTypedRich : F1.Occupancy.State :=
  {domainRich with flat := {domainRich.flat with semantic := {domainRich.flat.semantic with
    occupancy := fun l => if l = ⟨17⟩ then .live ⟨⟨17⟩,⟨1⟩,⟨1⟩,⟨17⟩,domain⟩ else .vacant}}}
theorem invented_rich_typed_root_rejected :
    ¬ RefinesDomain context after OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot forgedTypedRich OneBackingIssuerWitness.afterInterpretation typing slotHandle := by
  intro ref
  have vacancy := (no_typed_root_or_incarnation ref).1 ⟨17⟩
  simp [forgedTypedRich] at vacancy

/-- F0 has no used-domain history. Recycled retired D=0 is rich WF, but is
rejected by the actual source-generated D=1 inventory/refinement. -/
def recycledRich := richIssue richSlot ⟨0⟩ ⟨value⟩
theorem retired_D_live_freshness_is_insufficient :
    WellFormed OneBackingIssuerWitness.afterGeometry typing.layout recycledRich ∧
    ¬ RefinesDomain context after OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot recycledRich OneBackingIssuerWitness.afterInterpretation typing slotHandle := by
  refine ⟨rich_issue_wellFormed complete_successor.2.2.2.2.2.2,?_⟩
  intro ref
  have h : ({⟨0⟩} : Finset DomainId) = {⟨1⟩} := ref.domains
  have member : (⟨0⟩ : DomainId) ∈ ({⟨0⟩} : Finset DomainId) := Finset.mem_singleton_self _
  rw [h] at member
  have denied : (⟨0⟩ : DomainId) ∉ ({⟨1⟩} : Finset DomainId) := by decide
  exact denied member

end
end NewLang.Adjunct.FreshDomainCounterexample
