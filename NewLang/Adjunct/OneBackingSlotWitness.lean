import NewLang.Adjunct.OneBackingSlotRich

namespace NewLang.Adjunct.OneBackingSlotWitness
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource OneBackingSlotSource OneBackingSlotRich
noncomputable section

def context : Context := ⟨OneBackingIssuerWitness.target,OneBackingIssuerWitness.beforeSource,OneBackingIssuerWitness.ok⟩
def typing : Typing context := ⟨⟨0⟩,OneBackingIssuerWitness.layout,rfl⟩
def slotHandle : ClaimId := ⟨10⟩
def someSource := start context
def backingSource := matchPost context someSource
def rawSource := destructurePost context backingSource
def slotSource := slotPost context rawSource
def richSlot := slotRichPost context OneBackingIssuerWitness.afterInterpretation typing slotHandle OneBackingIssuerWitness.afterRich

theorem fresh_slot : slotHandle ∉ OneBackingIssuerWitness.afterRich.ledger.active := by
  simp [slotHandle,OneBackingIssuerWitness.afterRich,OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,
    OneBackingIssuerWitness.supply,OneBackingIssuerWitness.beforeRich,OneBackingIssuerWitness.oneRaw]

/-- The accepted F53 theorem constructs B's original issuance from a nonempty
old frame. All successor authority below is constructed from that POST. -/
theorem complete_successor :
    Dispatch context (.some 1007) someSource ∧
    Step context someSource backingSource ∧ Step context backingSource rawSource ∧
    IntoSlotRequest context .node rawSource slotSource ∧
    RawIntoSlot typing.layout (context.packet.observedAddress % context.target.alignofH = 0)
      OneBackingIssuerWitness.afterRich.ledger (rawHandle context OneBackingIssuerWitness.afterInterpretation) slotHandle typing.node
      (extent context OneBackingIssuerWitness.afterInterpretation) richSlot.ledger ∧
    RefinesSlot context slotSource OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich richSlot OneBackingIssuerWitness.afterInterpretation typing slotHandle ∧
    WellFormed OneBackingIssuerWitness.afterGeometry typing.layout richSlot :=
  some_post_to_slot (c := context) OneBackingIssuerWitness.before_source_wellFormed OneBackingIssuerWitness.concrete_some_simulation.2.2.1 typing
    OneBackingIssuerWitness.concrete_some_simulation.2.2.2 slotHandle fresh_slot

theorem source_chain_wellFormed :
    OneBackingSlotSource.SourceWF context someSource ∧
    OneBackingSlotSource.SourceWF context backingSource ∧
    OneBackingSlotSource.SourceWF context rawSource ∧
    OneBackingSlotSource.SourceWF context slotSource := by
  have s0 := start_wellFormed (c := context) OneBackingIssuerWitness.before_source_wellFormed
  have s1 := match_wellFormed OneBackingIssuerWitness.before_source_wellFormed s0 rfl
  have s2 := destructure_wellFormed OneBackingIssuerWitness.before_source_wellFormed s1 rfl
  exact ⟨s0,s1,s2,complete_successor.2.2.2.2.2.1.source⟩

/-- Two original nonCopy members after destructure; after conversion exactly
A_B and empty slot_B remain. The old nonempty C graph stays byte-for-byte. -/
theorem exact_current_graph_and_values :
    rawSource.current = {(1004,.allocationLocal),(1005,.rawLocal)} ∪ frame context ∧
    slotSource.current = {(1004,.allocationLocal),(1008,.slotLocal)} ∪ frame context ∧
    slotSource.allocation = some 1004 ∧ rawSource.raw = some ⟨1005,41,24⟩ ∧
    slotSource.raw = none ∧ slotSource.slot = some ⟨⟨1008,41,24⟩,.node⟩ ∧
    slotSource.consumedValues = {1007,1006,1005} ∧ slotSource.extras = ∅ := by
  refine ⟨source_chain_wellFormed.2.2.1.currentExact,
    source_chain_wellFormed.2.2.2.currentExact,rfl,rfl,rfl,rfl,?_,rfl⟩
  exact source_chain_wellFormed.2.2.2.consumed

theorem original_A_and_empty_slot :
    OneBackingIssuerWitness.afterInterpretation.allocation 1004 = some ⟨7⟩ ∧
    OneBackingIssuerWitness.afterInterpretation.allocation 1000 = some ⟨0⟩ ∧
    OneBackingIssuerWitness.afterInterpretation.region 41 = ⟨7⟩ ∧
    OneBackingIssuerWitness.afterInterpretation.region 40 = ⟨0⟩ ∧
    Has richSlot.ledger slotHandle (.slot typing.node ⟨⟨7⟩,⟨0,24⟩⟩) ∧
    Has richSlot.ledger ⟨0⟩ (.storage ⟨⟨0⟩,⟨0,24⟩⟩) ∧
    richSlot.ledger.active = {⟨10⟩,⟨0⟩} ∧ ⟨9⟩ ∉ richSlot.ledger.active := by
  have ref := complete_successor.2.2.2.2.2.1
  have old := ref.frame OneBackingIssuerWitness.oldGrant (Finset.mem_singleton_self _)
  refine ⟨?_,?_,?_,?_,ref.packet,old,?_,?_⟩
  all_goals simp [OneBackingIssuerWitness.afterInterpretation,interpretationPost,OneBackingIssuerWitness.beforeSource,OneBackingIssuerWitness.beforeInterpretation,
    OneBackingIssuerWitness.supply,richSlot,slotRichPost,consumeOne,rawHandle,context,Context.packet,freshGrant,
    OneBackingIssuerWitness.afterRich,OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,OneBackingIssuerWitness.beforeRich,OneBackingIssuerWitness.oneRaw,slotHandle]

/-- Rich physical/semantic state and scope are fixed by conversion, including
all old/new bytes. No type lifetime, placement, domain, pointer or loan appears. -/
theorem fixed_world_and_footprint :
    richSlot.flat = OneBackingIssuerWitness.afterRich.flat ∧ richSlot.ledger.scope = OneBackingIssuerWitness.afterRich.ledger.scope ∧
    richSlot.flat.semantic = F0.State.empty ∧
    richSlot.flat.physical.placement = (fun _ => none) ∧
    TotalFootprint OneBackingIssuerWitness.afterGeometry richSlot.ledger = TotalFootprint OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich.ledger ∧
    Accounting OneBackingIssuerWitness.afterGeometry typing.layout (FlatLive richSlot.flat.semantic) richSlot.flat.physical richSlot.ledger := by
  have ref := complete_successor.2.2.2.2.2.1
  have raw := complete_successor.2.2.2.2.1
  exact ⟨rfl,rfl,ref.flat ▸ ref.issuance.semanticEmpty,ref.flat ▸ ref.issuance.placementEmpty,
    into_slot_conserves_all_byte_responsibility _ raw,complete_successor.2.2.2.2.2.2.accounting⟩

end
end NewLang.Adjunct.OneBackingSlotWitness
