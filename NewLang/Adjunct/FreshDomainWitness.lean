import NewLang.Adjunct.FreshDomainRich

namespace NewLang.Adjunct.FreshDomainWitness
open F0 F1.Backing F1.Occupancy OneBackingSlotSource OneBackingSlotRich FreshDomainRich
open OneBackingSlotWitness
noncomputable section

/-- A retired D=0 and value=7, neither currently live. This source history is
NOT inferred from R_C=0, address, Copy ptr or accepted F0 (which lacks D history). -/
def history : FreshDomainSource.History context :=
  ⟨1,{⟨0⟩},{7},by intro d m; simp only [Finset.mem_singleton] at m; subst d; decide,
    by intro v m; simp only [Finset.mem_singleton] at m; subst v; decide⟩
def before := FreshDomainSource.start context slotSource history
def after := FreshDomainSource.issuePost before
def domain : DomainId := FreshDomainSource.newDomain before
def value : Nat := FreshDomainSource.newValue before
def domainRich := richIssue richSlot domain ⟨value⟩

theorem before_refines :
    RefinesDomain context before OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot richSlot OneBackingIssuerWitness.afterInterpretation typing slotHandle :=
  start_refines (c := context) OneBackingIssuerWitness.before_source_wellFormed
    complete_successor.2.2.2.2.2.1 rfl history

theorem complete_issue :
    FreshDomainSource.Issue context before after ∧
    RefinesDomain context after OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot domainRich OneBackingIssuerWitness.afterInterpretation typing slotHandle ∧
    WellFormed OneBackingIssuerWitness.afterGeometry typing.layout domainRich :=
  issue_simulation before_refines complete_successor.2.2.2.2.2.2 rfl rfl

theorem actual_fresh_D_available :
    domain = ⟨1⟩ ∧ value = 1009 ∧
    before.available = ∅ ∧ before.outgoing = ∅ ∧
    before.usedDomains = {⟨0⟩} ∧ domain ∉ before.usedDomains ∧
    after.available = {(domain,value)} ∧ after.outgoing = ∅ ∧
    domainRich.flat.semantic.liveDomains = {domain} ∧
    domainRich.flat.semantic.domainValueCarrier domain = some ⟨value⟩ ∧
    (⟨0⟩ : DomainId) ∉ domainRich.flat.semantic.liveDomains := by
  have fresh := FreshDomainSource.issue_derives_fresh_unique_available complete_issue.1
  exact ⟨rfl,rfl,rfl,rfl,rfl,fresh.1,fresh.2.2.1,fresh.2.2.2.1,rfl,
    by simp [domainRich,richIssue,semanticIssue],by decide⟩

/-- No domain issuance bytes/claim/root hidden in this nonempty C+B witness. -/
theorem owner_and_nonempty_rich_frame :
    after.owners = slotSource ∧ after.owners.allocation = some 1004 ∧
    after.owners.slot = some ⟨⟨1008,41,24⟩,.node⟩ ∧ after.owners.raw = none ∧
    domainRich.ledger = richSlot.ledger ∧ domainRich.flat.physical = richSlot.flat.physical ∧
    domainRich.ledger.active = {⟨10⟩,⟨0⟩} ∧
    Has domainRich.ledger ⟨0⟩ (.storage ⟨⟨0⟩,⟨0,24⟩⟩) ∧
    Has domainRich.ledger slotHandle (.slot typing.node ⟨⟨7⟩,⟨0,24⟩⟩) ∧
    TotalFootprint OneBackingIssuerWitness.afterGeometry domainRich.ledger =
      TotalFootprint OneBackingIssuerWitness.afterGeometry richSlot.ledger :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,original_A_and_empty_slot.2.2.2.2.2.2.1,
    original_A_and_empty_slot.2.2.2.2.2.1,original_A_and_empty_slot.2.2.2.2.1,rfl⟩

theorem no_typed_Node_before_initialize :
    (∀ l, domainRich.flat.semantic.occupancy l = .vacant) ∧
    domainRich.flat.semantic.usedIncarnations = ∅ ∧ after.extras = ∅ :=
  no_typed_root_or_incarnation complete_issue.2.1

/-- Exact missing interface: a live D and current original Domain carrier do
not yield the lexical Domain-value ref in accepted object-ref semantics. -/
theorem lexical_domain_loan_first_bridge_unproved (stable access : Prop) (p : PtrToken) :
    domain ∈ domainRich.flat.semantic.liveDomains ∧
    domainRich.flat.semantic.domainValueCarrier domain = some ⟨value⟩ ∧
    ¬ AcquireRef stable access domainRich.flat.semantic p domain :=
  ⟨by simp [domainRich,richIssue,semanticIssue],by simp [domainRich,richIssue,semanticIssue],
    domain_value_has_no_accepted_object_ref complete_issue.2.1 stable access p domain⟩

end
end NewLang.Adjunct.FreshDomainWitness
