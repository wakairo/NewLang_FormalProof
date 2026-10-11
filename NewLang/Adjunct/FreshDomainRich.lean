import NewLang.Adjunct.FreshDomainSource
import NewLang.F0.Domain

namespace NewLang.Adjunct.FreshDomainRich
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource OneBackingSlotSource OneBackingSlotRich
noncomputable section

/-- Adjunct introduction, NOT an existing accepted rich transition. Unlike a
mere ghost marker it constructs the accepted live-domain/carrier state. No
object/package/root/ptr is introduced. Source inventory supplies nonCopy law. -/
def semanticIssue (s : F0.State) (d : DomainId) (v : DomainValueCarrierId) : F0.State :=
  {s with
    liveDomains := insert d s.liveDomains
    domainValueCarrier := fun q => if q = d then some v else s.domainValueCarrier q}

theorem semantic_issue_wellFormed {s d v} (wf : F0.WellFormed s) :
    F0.WellFormed (semanticIssue s d v) := by
  constructor
  · exact wf.carrierUnique
  · exact wf.placesUnique
  · exact wf.incarnationsUnique
  · exact wf.packagesPresent
  · intro l r live; exact Finset.mem_insert_of_mem (wf.domainsValid l r live)
  · intro pkg value survives present fact dep
    have live := wf.dependenciesValid pkg value survives present fact dep
    cases fact with
    | valueFact p f => exact live
    | domainLive q => exact Finset.mem_insert_of_mem live
  · exact wf.valueFactsRecorded
  · exact wf.incarnationsRecorded
  · intro q
    by_cases eq : q = d
    · subst q; simp [semanticIssue]
    · simpa [semanticIssue,eq] using wf.domainCarrierCoherent q

/-- World/geometry/physical placement and ledger are passed through unchanged. -/
def richIssue (s : F1.Occupancy.State) (d : DomainId) (v : DomainValueCarrierId) : F1.Occupancy.State :=
  ⟨⟨semanticIssue s.flat.semantic d v,s.flat.physical⟩,s.ledger⟩

theorem rich_issue_wellFormed {g layout s d v} (wf : WellFormed g layout s) :
    WellFormed g layout (richIssue s d v) :=
  ⟨semantic_issue_wellFormed wf.toWellFormed,wf.accounting⟩

/-- F55 is a HISTORICAL slot certificate. Its semanticEmpty/flat equality is
not falsely asserted of CURRENT rich state once D is live. The new relation
uses accepted liveDomains/carrier maps plus explicit source authority.
There is NO accepted scoped loan/ref object or stability capability here. -/
structure RefinesDomain (c : Context) (s : FreshDomainSource.State) (g : Geometry)
    (issuerBirth slotBirth rich : F1.Occupancy.State) (i : Interpretation)
    (t : Typing c) (slotHandle : ClaimId) : Prop where
  source : FreshDomainSource.SourceWF c s
  slotCertificate : RefinesSlot c s.owners g issuerBirth slotBirth i t slotHandle
  physical : rich.flat.physical = slotBirth.flat.physical
  ledger : rich.ledger = slotBirth.ledger
  occupancy : rich.flat.semantic.occupancy = slotBirth.flat.semantic.occupancy
  packages : rich.flat.semantic.packages = slotBirth.flat.semantic.packages
  loose : rich.flat.semantic.loosePackages = slotBirth.flat.semantic.loosePackages
  facts : rich.flat.semantic.usedValueFacts = slotBirth.flat.semantic.usedValueFacts
  incarnations : rich.flat.semantic.usedIncarnations = slotBirth.flat.semantic.usedIncarnations
  domains : rich.flat.semantic.liveDomains = (FreshDomainSource.current s).image Prod.fst
  carriers : ∀ d v, (d,v) ∈ FreshDomainSource.current s ↔
    rich.flat.semantic.domainValueCarrier d = some ⟨v⟩

theorem start_refines {c owners g birth slotRich i t slotHandle}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (slotRef : RefinesSlot c owners g birth slotRich i t slotHandle)
    (slot : owners.phase = .slot) (history : FreshDomainSource.History c) :
    RefinesDomain c (FreshDomainSource.start c owners history) g birth slotRich slotRich i t slotHandle := by
  have empty := (no_early_typed_authority slotRef).1
  refine ⟨FreshDomainSource.start_wellFormed oldWF slotRef.source slot history,
    slotRef,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [FreshDomainSource.current,FreshDomainSource.start,empty,F0.State.empty]
  · intro d v
    simp [FreshDomainSource.current,FreshDomainSource.start,empty,F0.State.empty]

theorem empty_inventory_has_no_carrier {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle)
    (empty : FreshDomainSource.current s = ∅) :
    ∀ d, rich.flat.semantic.domainValueCarrier d = none := by
  intro d
  cases eq : rich.flat.semantic.domainValueCarrier d with
  | none => rfl
  | some v =>
    have member := (ref.carriers d v.index).mpr (by simpa using eq)
    rw [empty] at member; simp at member

/-- Issuer resource is a source event, not a pre-established rich D match.
Fresh D/value are computed from history counters before any current grant. -/
theorem issue_refines {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle)
    (empty : FreshDomainSource.current s = ∅) :
    RefinesDomain c (FreshDomainSource.issuePost s) g birth slotRich
      (richIssue rich (FreshDomainSource.newDomain s) ⟨FreshDomainSource.newValue s⟩) i t slotHandle := by
  have av := (FreshDomainSource.no_domain_implies_places_empty empty).1
  have out := (FreshDomainSource.no_domain_implies_places_empty empty).2
  have noCarrier := empty_inventory_has_no_carrier ref empty
  have noDomains : rich.flat.semantic.liveDomains = ∅ := by rw [ref.domains,empty]; simp
  refine ⟨FreshDomainSource.issue_wellFormed ref.source empty,ref.slotCertificate,
    ref.physical,ref.ledger,ref.occupancy,ref.packages,ref.loose,ref.facts,ref.incarnations,?_,?_⟩
  · simp [richIssue,semanticIssue,FreshDomainSource.current,FreshDomainSource.issuePost,av,out,noDomains]
  · intro d v
    simp [FreshDomainSource.current,FreshDomainSource.issuePost,av,out,richIssue,semanticIssue,noCarrier]
    by_cases eq : d = FreshDomainSource.newDomain s <;> simp [eq,eq_comm]

/-- Supported boundary: source authority and accepted rich live D are
constructed together, with original A/slot/R/claims and all accounting fixed. -/
theorem issue_simulation {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle)
    (wf : WellFormed g t.layout rich) (phase : s.phase = .ready)
    (empty : FreshDomainSource.current s = ∅) :
    FreshDomainSource.Issue c s (FreshDomainSource.issuePost s) ∧
    RefinesDomain c (FreshDomainSource.issuePost s) g birth slotRich
      (richIssue rich (FreshDomainSource.newDomain s) ⟨FreshDomainSource.newValue s⟩) i t slotHandle ∧
    WellFormed g t.layout (richIssue rich (FreshDomainSource.newDomain s) ⟨FreshDomainSource.newValue s⟩) :=
  ⟨⟨ref.source,phase,empty,rfl⟩,issue_refines ref empty,rich_issue_wellFormed wf⟩

theorem non_domain_frame {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle) :
    rich.flat.physical = slotRich.flat.physical ∧ rich.ledger = slotRich.ledger ∧
    TotalFootprint g rich.ledger = TotalFootprint g slotRich.ledger ∧
    i.allocation c.packet.base = some (extent c i).region ∧
    s.owners.allocation = some c.packet.base ∧
    (c.packet.base,Binding.allocationLocal) ∈ s.owners.current := by
  have original := original_A_available ref.slotCertificate ref.source.slot
  exact ⟨ref.physical,ref.ledger,congrArg (TotalFootprint g) ref.ledger,
    original.2.2,original.1,original.2.1⟩

/-- This is the exact first obstruction: accepted AcquireRef targets a live
OBJECT root, not an available Domain VALUE. Even a real live D and every
external stability/access proposition cannot supply the absent typed root. -/
theorem domain_value_has_no_accepted_object_ref {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle)
    (stable access : Prop) (ptr : PtrToken) (d : DomainId) :
    ¬ AcquireRef stable access rich.flat.semantic ptr d := by
  intro acquired
  rcases acquired.2.target with ⟨root,live,_,_⟩
  rw [ref.occupancy,(no_early_typed_authority ref.slotCertificate).1] at live
  simp [F0.State.empty] at live

theorem no_typed_root_or_incarnation {c s g birth slotRich rich i t slotHandle}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle) :
    (∀ l, rich.flat.semantic.occupancy l = .vacant) ∧
    rich.flat.semantic.usedIncarnations = ∅ ∧ s.extras = ∅ := by
  have empty := (no_early_typed_authority ref.slotCertificate).1
  refine ⟨?_,?_,ref.source.noEarly⟩
  · intro l; rw [ref.occupancy,empty]; rfl
  · rw [ref.incarnations,empty]; rfl

/-- Source placement forwarding preserves this deliberately coarse rich
projection. It does not prove a known-call or lexical-loan applicability rule. -/
theorem forward_refines {c s g birth slotRich rich i t slotHandle d v}
    (ref : RefinesDomain c s g birth slotRich rich i t slotHandle)
    (available : (d,v) ∈ s.available) :
    RefinesDomain c (FreshDomainSource.forwardPost s d v) g birth slotRich rich i t slotHandle := by
  have same := FreshDomainSource.forward_current available
  refine ⟨FreshDomainSource.forward_wellFormed ref.source available,ref.slotCertificate,
    ref.physical,ref.ledger,ref.occupancy,ref.packages,ref.loose,ref.facts,ref.incarnations,?_,?_⟩
  · rw [same]; exact ref.domains
  · intro d v; rw [same]; exact ref.carriers d v

end
end NewLang.Adjunct.FreshDomainRich
