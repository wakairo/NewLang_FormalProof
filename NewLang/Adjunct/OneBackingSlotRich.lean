import NewLang.Adjunct.OneBackingSlotSource
import NewLang.F1.Occupancy.Conversion

namespace NewLang.Adjunct.OneBackingSlotRich
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource OneBackingSlotSource
noncomputable section

/-- Authorized static interpretation of the selected Node. Neither sizeof nor
nominal lookup is a theorem about native ABI or the production checker. -/
structure Typing (c : Context) where
  node : TypeId
  layout : Layout
  size : layout.size node = c.target.sizeofH

def issued (c : Context) : Source := somePost c.target c.old c.ok
def extent (c : Context) (i : Interpretation) : Extent :=
  ⟨i.region c.packet.region,⟨0,c.packet.n⟩⟩
def rawHandle (c : Context) (i : Interpretation) : ClaimId := i.rawClaim (c.packet.base+1)
def frameHandles (c : Context) (i : Interpretation) : Finset ClaimId :=
  c.old.grants.image (fun p => i.rawClaim (p.base+1))
def packetHandle (c : Context) (i : Interpretation) (slot : ClaimId) : Phase → ClaimId
  | .slot => slot
  | _ => rawHandle c i

def packetClaim (c : Context) (i : Interpretation) (t : Typing c) : Phase → Claim
  | .slot => .slot t.node (extent c i)
  | _ => .storage (extent c i)

/-- The birth certificate is HISTORICAL issuer POST, not additional CURRENT
storage. Dynamic current authority is exclusively the Has/inventory fields.
The fixed i interprets original A; the slot ghost handle is supplied fresh,
without supplying any ready slot claim. -/
structure RefinesSlot (c : Context) (s : Custody) (g : Geometry)
    (birth rich : F1.Occupancy.State) (i : Interpretation) (t : Typing c)
    (slot : ClaimId) : Prop where
  source : OneBackingSlotSource.SourceWF c s
  issuance : Refines (issued c) g birth i
  flat : rich.flat = birth.flat
  scope : rich.ledger.scope = birth.ledger.scope
  frame : ∀ p ∈ c.old.grants,
    Has rich.ledger (i.rawClaim (p.base+1)) (.storage ⟨i.region p.region,⟨0,p.n⟩⟩)
  packet : Has rich.ledger (packetHandle c i slot s.phase) (packetClaim c i t s.phase)
  active : rich.ledger.active = insert (packetHandle c i slot s.phase) (frameHandles c i)

/-- Allocation identity and full extent are derived from issuer provenance,
not an independent matched A/slot assumption. -/
theorem original_allocation_and_full_range {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) :
    i.allocation c.packet.base = some (extent c i).region ∧
    (extent c i).range.base = 0 ∧ (extent c i).range.length = c.target.sizeofH ∧
    g.capacity (extent c i).region = (extent c i).range.length := by
  have mem : c.packet ∈ (issued c).grants := Finset.mem_insert_self _ _
  exact ⟨ref.issuance.allocationOrigin _ mem,rfl,rfl,ref.issuance.exactCapacity _ mem⟩

theorem start_refines {c g birth i} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : Refines (issued c) g birth i) (t : Typing c) (slot : ClaimId) :
    RefinesSlot c (start c) g birth birth i t slot := by
  refine ⟨start_wellFormed oldWF,ref,rfl,rfl,?_,?_,?_⟩
  · intro p pm; exact ref.fullRaw p (Finset.mem_insert_of_mem pm)
  · exact ref.fullRaw c.packet (Finset.mem_insert_self _ _)
  · simpa [issued,somePost,Finset.image_insert,packetHandle,rawHandle,frameHandles,start,Context.packet]
      using ref.claimInventory

theorem match_refines {c s g birth rich i t slot}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .some) :
    RefinesSlot c (matchPost c s) g birth rich i t slot := by
  refine ⟨match_wellFormed oldWF ref.source phase,ref.issuance,ref.flat,ref.scope,ref.frame,?_,?_⟩
  · simpa [matchPost,phase,packetHandle,packetClaim] using ref.packet
  · simpa [matchPost,phase,packetHandle] using ref.active

theorem destructure_refines {c s g birth rich i t slot}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .backing) :
    RefinesSlot c (destructurePost c s) g birth rich i t slot := by
  refine ⟨destructure_wellFormed oldWF ref.source phase,ref.issuance,ref.flat,ref.scope,ref.frame,?_,?_⟩
  · simpa [destructurePost,phase,packetHandle,packetClaim] using ref.packet
  · simpa [destructurePost,phase,packetHandle] using ref.active

/-- Fresh lineage distinguishes new B from every older C, including retired
history. Sharing a claim handle would equate their regions, a contradiction. -/
theorem new_raw_not_frame {c s g birth rich i t slot}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .raw) :
    rawHandle c i ∉ frameHandles c i := by
  intro mem
  rcases Finset.mem_image.mp mem with ⟨p,pm,eq⟩
  have old := ref.frame p pm
  have new := ref.packet
  simp only [phase,packetHandle,packetClaim] at new
  have same : Claim.storage ⟨i.region p.region,⟨0,p.n⟩⟩ = .storage (extent c i) :=
    old.2.symm.trans (eq ▸ new.2)
  have regions : i.region p.region = i.region c.packet.region :=
    congrArg (fun claim => claim.extent.region) same
  have pb := oldWF.regionBelow p pm
  have original : p.region = c.packet.region := ref.issuance.lineageUnique
    p.region (by change p.region < c.old.nextRegion+1; omega)
    c.packet.region (by change c.old.nextRegion < c.old.nextRegion+1; omega) regions
  change p.region = c.old.nextRegion at original
  omega

def slotRichPost (c : Context) (i : Interpretation) (t : Typing c) (slot : ClaimId)
    (rich : F1.Occupancy.State) : F1.Occupancy.State :=
  ⟨rich.flat,consumeOne rich.ledger (rawHandle c i) slot (.slot t.node (extent c i))⟩

/-- Construct the accepted raw transition: full Has comes from the CURRENT
raw carrier, exact size/alignment from issuer plus authorized Node layout.
POST is a computed consumeOne, never a premise. -/
theorem construct_raw_into_slot {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .raw)
    (fresh : slot ∉ rich.ledger.active) :
    RawIntoSlot t.layout (c.packet.observedAddress % c.target.alignofH = 0)
      rich.ledger (rawHandle c i) slot t.node (extent c i)
      (slotRichPost c i t slot rich).ledger := by
  refine ⟨?_,fresh,?_,c.ok.aligned,rfl⟩
  · simpa [phase,packetHandle,packetClaim] using ref.packet
  · change c.target.sizeofH = t.layout.size t.node; exact t.size.symm

theorem slot_rich_wellFormed {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .raw)
    (wf : WellFormed g t.layout rich) (fresh : slot ∉ rich.ledger.active) :
    WellFormed g t.layout (slotRichPost c i t slot rich) :=
  empty_claim_conversion_preserves_flat wf
    (into_slot_step_of_raw wf.accounting (construct_raw_into_slot ref phase fresh)).2.2

theorem slot_refines {c s g birth rich i t slot}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .raw)
    (fresh : slot ∉ rich.ledger.active) :
    RefinesSlot c (slotPost c s) g birth (slotRichPost c i t slot rich) i t slot := by
  have notFrame := new_raw_not_frame oldWF ref phase
  have inventory : rich.ledger.active = insert (rawHandle c i) (frameHandles c i) := by
    simpa [phase,packetHandle] using ref.active
  refine ⟨slot_wellFormed oldWF ref.source phase,ref.issuance,ref.flat,ref.scope,?_,?_,?_⟩
  · intro p pm
    have old := ref.frame p pm
    have oldFrame : i.rawClaim (p.base+1) ∈ frameHandles c i := Finset.mem_image.mpr ⟨p,pm,rfl⟩
    have notRaw : i.rawClaim (p.base+1) ≠ rawHandle c i := by
      intro eq; exact notFrame (eq ▸ oldFrame)
    have notSlot : i.rawClaim (p.base+1) ≠ slot := by intro eq; exact fresh (eq ▸ old.1)
    exact ⟨consumeOne_active_iff.mpr (Or.inr ⟨notRaw,old.1⟩),by
      simpa [slotRichPost,consumeOne,notSlot] using old.2⟩
  · exact consumeOne_produces_result _ _ _ _
  · change insert slot (rich.ledger.active.erase (rawHandle c i)) = insert slot (frameHandles c i)
    rw [inventory,Finset.erase_insert notFrame]

/-- Simultaneous source and accepted-rich conversion. The graph and ledger
updates are independent definitions; refinement/WF are their derived POST. -/
theorem raw_to_slot_simulation {c s g birth rich i t slot}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .raw)
    (wf : WellFormed g t.layout rich) (fresh : slot ∉ rich.ledger.active) :
    IntoSlotRequest c .node s (slotPost c s) ∧
    RawIntoSlot t.layout (c.packet.observedAddress % c.target.alignofH = 0)
      rich.ledger (rawHandle c i) slot t.node (extent c i) (slotRichPost c i t slot rich).ledger ∧
    RefinesSlot c (slotPost c s) g birth (slotRichPost c i t slot rich) i t slot ∧
    WellFormed g t.layout (slotRichPost c i t slot rich) :=
  ⟨⟨rfl,phase,Step.intoSlot s ref.source phase rfl c.ok.aligned⟩,
    construct_raw_into_slot ref phase fresh,slot_refines oldWF ref phase fresh,
    slot_rich_wellFormed ref phase wf fresh⟩

/-- Immediate successor of F53 Some POST. No matched new A, slot, or updated
carrier/ledger is a PRE hypothesis. Historical issuer refinement is allowed. -/
theorem some_post_to_slot {c g birth i}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (issuer : Refines (issued c) g birth i) (t : Typing c)
    (wf : WellFormed g t.layout birth) (slot : ClaimId) (fresh : slot ∉ birth.ledger.active) :
    Dispatch c (.some (c.old.nextValue+3)) (start c) ∧
    Step c (start c) (matchPost c (start c)) ∧
    Step c (matchPost c (start c)) (destructurePost c (matchPost c (start c))) ∧
    IntoSlotRequest c .node (destructurePost c (matchPost c (start c)))
      (slotPost c (destructurePost c (matchPost c (start c)))) ∧
    RawIntoSlot t.layout (c.packet.observedAddress % c.target.alignofH = 0)
      birth.ledger (rawHandle c i) slot t.node (extent c i) (slotRichPost c i t slot birth).ledger ∧
    RefinesSlot c (slotPost c (destructurePost c (matchPost c (start c)))) g birth
      (slotRichPost c i t slot birth) i t slot ∧
    WellFormed g t.layout (slotRichPost c i t slot birth) := by
  have r0 := start_refines oldWF issuer t slot
  have r1 := match_refines oldWF r0 rfl
  have r2 := destructure_refines oldWF r1 rfl
  exact ⟨Dispatch.some,Step.matchSome _ r0.source rfl,Step.destructure _ r1.source rfl,
    raw_to_slot_simulation oldWF r2 rfl wf fresh⟩

/-- From PRE issuer inputs, not a ready-made successful issuance or slot.
The two fresh ghost names select claim IDs, not source runtime allocations. -/
theorem issuer_to_slot {target old g layout before i}
    (oldWF : OneBackingIssuerSource.SourceWF old) (bounded : old.grants.card ≤ 1)
    (beforeWF : WellFormed g layout before) (beforeRef : Refines old g before i)
    (ok : Success target) (supply : OneBackingIssuerRich.Supply g before)
    (size : supply.n = target.sizeofH) (history : supply.region ∉ i.usedRegions)
    (t : Typing (⟨target,old,ok⟩ : Context)) (layoutEq : t.layout = layout)
    (slot : ClaimId) (fresh : slot ∉ before.ledger.active) (different : slot ≠ supply.claim) :
    let c : Context := ⟨target,old,ok⟩
    let birth := OneBackingIssuerRich.post supply
    let g' := OneBackingIssuerRich.geometry supply
    let i' := interpretationPost supply old i
    OneBackingIssuerSource.Step target old (.some (old.nextValue+3)) (issued c) ∧
    RefinesSlot c (slotPost c (destructurePost c (matchPost c (start c)))) g' birth
      (slotRichPost c i' t slot birth) i' t slot ∧
    WellFormed g' t.layout (slotRichPost c i' t slot birth) := by
  dsimp only
  have issuance := some_simulation oldWF bounded beforeWF beforeRef ok supply size history
  have slotFresh : slot ∉ (OneBackingIssuerRich.post supply).ledger.active := by
    simp [OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,different,fresh]
  have birthWF : WellFormed (OneBackingIssuerRich.geometry supply) t.layout
      (OneBackingIssuerRich.post supply) := by rw [layoutEq]; exact issuance.2.2.2
  have successor := some_post_to_slot (c := ⟨target,old,ok⟩) oldWF issuance.2.2.1 t birthWF slot slotFresh
  exact ⟨issuance.1,successor.2.2.2.2.2⟩

/-- Derive unique current empty slot from the operationally proved source graph.
No prior frame edge can be a newly generated slot-local binding. -/
theorem exactly_one_current_slot {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .slot) :
    ∀ v, (v,Binding.slotLocal) ∈ s.current ↔ v = c.packet.base+4 := by
  intro v
  rw [ref.source.currentExact,phase]
  simp [packetGraph,OneBackingSlotSource.frame,liftEdges]

/-- Fixed historical issuance + equality of current flat state explicitly rule
out typed roots and placements; source extras rule out fresh D/ptr/loans. -/
theorem no_early_typed_authority {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) :
    rich.flat.semantic = F0.State.empty ∧ rich.flat.physical.placement = (fun _ => none) ∧ s.extras = ∅ := by
  rw [ref.flat]
  exact ⟨ref.issuance.semanticEmpty,ref.issuance.placementEmpty,ref.source.noEarly⟩

/-- Exact original A remains AVAILABLE, paired with the same region as the
current empty slot; this is not a deallocation or Domain capability theorem. -/
theorem original_A_available {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .slot) :
    s.allocation = some c.packet.base ∧
    (c.packet.base,Binding.allocationLocal) ∈ s.current ∧
    i.allocation c.packet.base = some (extent c i).region := by
  refine ⟨?_,?_,(original_allocation_and_full_range ref).1⟩
  · simpa [phase,expectedAllocation] using ref.source.allocation
  · rw [ref.source.currentExact,phase]; simp [packetGraph]

/-- Accepted Accounting forbids any second current slot claim covering the
same full extent, even if it is presented under another type/ghost handle. -/
theorem unique_full_slot_claim {c s g birth rich i t slot}
    (ref : RefinesSlot c s g birth rich i t slot) (phase : s.phase = .slot)
    (wf : WellFormed g t.layout rich) {id : ClaimId} {otherType : TypeId}
    (other : Has rich.ledger id (.slot otherType (extent c i))) : id = slot := by
  by_contra different
  have current : Has rich.ledger slot (.slot t.node (extent c i)) := by
    simpa [phase,packetHandle,packetClaim] using ref.packet
  apply nonempty_claim_cannot_be_covered_twice wf.accounting other.1 current.1 different
  rw [other.2,current.2]; exact Finset.Subset.refl _

end
end NewLang.Adjunct.OneBackingSlotRich
