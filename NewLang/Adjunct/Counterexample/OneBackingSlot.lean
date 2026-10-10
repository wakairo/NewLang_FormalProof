import NewLang.Adjunct.OneBackingSlotWitness
import NewLang.Adjunct.Counterexample.OneBackingIssuer

namespace NewLang.Adjunct.OneBackingSlotCounterexample
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource OneBackingSlotSource OneBackingSlotRich
open OneBackingSlotWitness
noncomputable section

/-- Replace the newly extracted original A by the old C value. Rich byte
accounting alone remains WF; source identity is an independent obligation. -/
def wrongA : Custody := {slotSource with allocation := some 1000}
theorem wrong_A_rejected_while_rich_wf :
    ¬ OneBackingSlotSource.SourceWF context wrongA ∧ WellFormed OneBackingIssuerWitness.afterGeometry typing.layout richSlot := by
  refine ⟨?_,complete_successor.2.2.2.2.2.2⟩
  intro wf
  have h : (some 1000 : Option Nat) = some 1004 := wf.allocation
  cases h

def shortRaw : Custody := {rawSource with raw := some ⟨1005,41,23⟩}
theorem short_source_raw_rejected : ¬ OneBackingSlotSource.SourceWF context shortRaw := by
  intro wf
  have h : (some ⟨1005,41,23⟩ : Option RawValue) = some ⟨1005,41,24⟩ := wf.raw
  cases h

/-- Exact-size refusal is independent of any attempted POST or claim freshness. -/
theorem short_rich_range_rejected (post : Ledger) :
    ¬ RawIntoSlot typing.layout True OneBackingIssuerWitness.afterRich.ledger ⟨9⟩ slotHandle
      typing.node ⟨⟨7⟩,⟨0,23⟩⟩ post := by
  intro raw
  have h : (23 : Nat) = 24 := raw.exactSize
  omega

/-- Accepted rich 3+1 controls are fully WF and conserve all four bytes, yet
neither current handle can be converted as ONE full Storage. -/
theorem accepted_three_plus_one_cannot_into_full_slot
    (layout : Layout) (aligned : Prop) (id result : ClaimId) (t : TypeId) (post : Ledger) :
    WellFormed F1.Occupancy.Counterexample.geometry F1.Occupancy.Counterexample.layout
      ⟨F1.Occupancy.Counterexample.rawState.flat,OneBackingIssuerBoundary.lastByteLedger⟩ ∧
    ¬ RawIntoSlot layout aligned OneBackingIssuerBoundary.lastByteLedger id result t
      F1.Occupancy.Counterexample.full post :=
  ⟨OneBackingIssuerCounterexample.accepted_three_plus_one_is_not_one_full_storage.1,
    fun raw => OneBackingIssuerCounterexample.accepted_three_plus_one_is_not_one_full_storage.2
      ⟨id,raw.sourceClaim⟩⟩

def duplicateSlot : Custody :=
  {slotSource with current := insert (1008,.extra 99) slotSource.current}
theorem duplicate_slot_rejected : ¬ OneBackingSlotSource.SourceWF context duplicateSlot := by
  intro wf
  have old : (1008,Binding.slotLocal) ∈ slotSource.current := by
    rw [exact_current_graph_and_values.2.1]; simp
  have h := wf.unique 1008 (.extra 99) .slotLocal (by simp [duplicateSlot])
    (Finset.mem_insert_of_mem old)
  cases h

/-- Dropping original A is detected even though slot byte coverage is unchanged. -/
def lostA : Custody := {slotSource with current := slotSource.current.erase (1004,.allocationLocal)}
theorem lost_A_rejected : ¬ OneBackingSlotSource.SourceWF context lostA := by
  intro wf
  have present : (1004,Binding.allocationLocal) ∈ lostA.current := by
    rw [wf.currentExact]; simp [lostA,slotSource,slotPost,packetGraph,context,Context.packet,freshGrant,OneBackingIssuerWitness.beforeSource]
  simp [lostA] at present

/-- A still-current raw alongside the newly produced slot is not a valid POST. -/
def retainedRaw : Custody := {slotSource with current := insert (1005,.rawLocal) slotSource.current}
theorem retained_raw_rejected : ¬ OneBackingSlotSource.SourceWF context retainedRaw := by
  intro wf
  have present : (1005,Binding.rawLocal) ∈ retainedRaw.current := by simp [retainedRaw]
  rw [wf.currentExact] at present
  simp [retainedRaw,slotSource,slotPost,packetGraph,frame,liftEdges,context,Context.packet,
    freshGrant,OneBackingIssuerWitness.beforeSource,OneBackingIssuerWitness.oldGrant,Grant.edges] at present

/-- A stale consumed wrapper is also rejected, even with intact byte claims. -/
def ghostBacking : Custody := {slotSource with current := insert (1006,.backingLocal) slotSource.current}
theorem ghost_backing_rejected : ¬ OneBackingSlotSource.SourceWF context ghostBacking := by
  intro wf
  have present : (1006,Binding.backingLocal) ∈ ghostBacking.current := by simp [ghostBacking]
  rw [wf.currentExact] at present
  simp [ghostBacking,slotSource,slotPost,packetGraph,frame,liftEdges,context,Context.packet,
    freshGrant,OneBackingIssuerWitness.beforeSource,OneBackingIssuerWitness.oldGrant,Grant.edges] at present

def staleSlot : Custody := {slotSource with slot := some ⟨⟨1008,0,24⟩,.node⟩}
theorem stale_source_region_rejected : ¬ OneBackingSlotSource.SourceWF context staleSlot := by
  intro wf
  have h : (some ⟨⟨1008,0,24⟩,.node⟩ : Option SlotValue) = some ⟨⟨1008,41,24⟩,.node⟩ := wf.slot
  cases h

/-- This control attacks the *interpretation*, not just a source descriptor:
substituting old R_C for original A_B fails the issuer-derived origin equation. -/
def wrongInterpretation : Interpretation :=
  {OneBackingIssuerWitness.afterInterpretation with
    allocation := fun v => if v = 1004 then some ⟨0⟩ else OneBackingIssuerWitness.afterInterpretation.allocation v}
theorem wrong_A_region_interpretation_rejected :
    ¬ RefinesSlot context slotSource OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      richSlot wrongInterpretation typing slotHandle := by
  intro ref
  have h := (original_allocation_and_full_range ref).1
  have h' : (some ⟨0⟩ : Option BackingRegionId) = some ⟨7⟩ := h
  cases h'

/-- Rich allocation freshness alone permits retired R=200; nominal history
rejects it before the successor. This is the inherited accepted countermodel. -/
theorem retired_R_rejected_despite_live_freshness :
    OneBackingIssuerCounterexample.staleSupply.region ∉ OneBackingIssuerWitness.beforeRich.flat.physical.world.liveRegions ∧
    OneBackingIssuerCounterexample.staleSupply.region ∈ OneBackingIssuerWitness.beforeInterpretation.usedRegions ∧
    ¬ Refines OneBackingIssuerWitness.afterSource
      (OneBackingIssuerRich.geometry OneBackingIssuerCounterexample.staleSupply)
      (OneBackingIssuerRich.post OneBackingIssuerCounterexample.staleSupply)
      (interpretationPost OneBackingIssuerCounterexample.staleSupply OneBackingIssuerWitness.beforeSource OneBackingIssuerWitness.beforeInterpretation) :=
  OneBackingIssuerCounterexample.stale_semantic_R_rejected_despite_live_freshness

def wrongTypeSlot : Custody := {slotSource with slot := some ⟨⟨1008,41,24⟩,.other⟩}
theorem incorrect_source_H_rejected :
    ¬ OneBackingSlotSource.SourceWF context wrongTypeSlot ∧ ¬ IntoSlotRequest context .other rawSource slotSource := by
  refine ⟨?_,other_request_rejected _ _ _⟩
  intro wf
  have h : (some ⟨⟨1008,41,24⟩,.other⟩ : Option SlotValue) = some ⟨⟨1008,41,24⟩,.node⟩ := wf.slot
  cases h

/-- Important control: accepted core checks the GIVEN type's layout, so another
same-size type passes it. Nominal Node identity must not be inferred from size. -/
def otherRich : F1.Occupancy.State :=
  ⟨OneBackingIssuerWitness.afterRich.flat,consumeOne OneBackingIssuerWitness.afterRich.ledger
    ⟨9⟩ slotHandle (.slot ⟨1⟩ (extent context OneBackingIssuerWitness.afterInterpretation))⟩
theorem same_size_other_H_passes_core :
    RawIntoSlot typing.layout True OneBackingIssuerWitness.afterRich.ledger ⟨9⟩ slotHandle ⟨1⟩
      (extent context OneBackingIssuerWitness.afterInterpretation) otherRich.ledger ∧
    WellFormed OneBackingIssuerWitness.afterGeometry typing.layout otherRich := by
  have raw : RawIntoSlot typing.layout True OneBackingIssuerWitness.afterRich.ledger ⟨9⟩ slotHandle ⟨1⟩
      (extent context OneBackingIssuerWitness.afterInterpretation) otherRich.ledger :=
    ⟨complete_successor.2.2.2.2.1.sourceClaim,fresh_slot,rfl,trivial,rfl⟩
  exact ⟨raw,empty_claim_conversion_preserves_flat OneBackingIssuerWitness.concrete_some_simulation.2.2.2
    (into_slot_step_of_raw OneBackingIssuerWitness.concrete_some_simulation.2.2.2.accounting raw).2.2⟩

theorem same_size_other_H_fails_refinement :
    ¬ RefinesSlot context slotSource OneBackingIssuerWitness.afterGeometry OneBackingIssuerWitness.afterRich
      otherRich OneBackingIssuerWitness.afterInterpretation typing slotHandle := by
  intro ref
  have h := ref.packet.2
  change Claim.slot ⟨1⟩ _ = Claim.slot ⟨0⟩ _ at h
  cases h

/-- None is a FULL identity issuer event with no dispatch edge to any successor;
the old raw C and original A_C remain. There is no caller B authority to refund. -/
theorem none_cannot_destructure_or_into_slot :
    OneBackingIssuerSource.Step OneBackingIssuerWitness.target OneBackingIssuerWitness.beforeSource .none OneBackingIssuerWitness.beforeSource ∧
    (∀ s, ¬ Dispatch context .none s) ∧
    OneBackingIssuerWitness.beforeInterpretation.allocation 1004 = none ∧
    Has OneBackingIssuerWitness.beforeRich.ledger ⟨0⟩ (.storage ⟨⟨0⟩,⟨0,24⟩⟩) :=
  ⟨OneBackingIssuerWitness.concrete_none_simulation.1,none_has_no_successor context,rfl,⟨by simp [OneBackingIssuerWitness.beforeRich,OneBackingIssuerWitness.oneRaw],rfl⟩⟩

/-- Duplicating a full empty-slot rich claim preserves coverage as a SET, but
accepted disjoint ownership accounting rejects it. -/
def duplicatedRich : F1.Occupancy.State :=
  ⟨richSlot.flat,{richSlot.ledger with
    active := insert ⟨11⟩ richSlot.ledger.active
    claim := fun id => if id = ⟨11⟩ then .slot typing.node (extent context OneBackingIssuerWitness.afterInterpretation)
      else richSlot.ledger.claim id}⟩
theorem duplicated_rich_slot_rejected :
    ¬ WellFormed OneBackingIssuerWitness.afterGeometry typing.layout duplicatedRich := by
  intro wf
  have old : Has duplicatedRich.ledger slotHandle
      (.slot typing.node (extent context OneBackingIssuerWitness.afterInterpretation)) := by
    refine ⟨Finset.mem_insert_of_mem complete_successor.2.2.2.2.2.1.packet.1,?_⟩
    simpa [duplicatedRich,slotHandle,packetHandle,packetClaim,slotSource,slotPost] using complete_successor.2.2.2.2.2.1.packet.2
  have new : Has duplicatedRich.ledger ⟨11⟩
      (.slot typing.node (extent context OneBackingIssuerWitness.afterInterpretation)) := by simp [Has,duplicatedRich]
  apply nonempty_claim_cannot_be_covered_twice wf.accounting new.1 old.1 (by decide)
  rw [new.2,old.2]

def staleRich : F1.Occupancy.State :=
  ⟨OneBackingIssuerWitness.afterRich.flat,consumeOne OneBackingIssuerWitness.afterRich.ledger
    ⟨9⟩ slotHandle (.slot typing.node ⟨⟨200⟩,⟨0,24⟩⟩)⟩
theorem stale_rich_region_rejected :
    ¬ WellFormed OneBackingIssuerWitness.afterGeometry typing.layout staleRich := by
  intro wf
  have slot := consumeOne_produces_result OneBackingIssuerWitness.afterRich.ledger ⟨9⟩ slotHandle
    (.slot typing.node ⟨⟨200⟩,⟨0,24⟩⟩)
  have member := wf.accounting.inScope slotHandle slot.1
  simp [staleRich,consumeOne,slotHandle,OneBackingIssuerWitness.afterRich,
    OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,OneBackingIssuerWitness.supply,
    OneBackingIssuerWitness.beforeRich,OneBackingIssuerWitness.oneRaw,Claim.extent] at member

/-- Some/OneBacking and raw cannot be consumed a second time after slot POST. -/
theorem terminal_slot_has_no_further_steps (post : Custody) : ¬ Step context slotSource post := by
  intro step
  cases step with
  | matchSome wf phase => cases phase
  | destructure wf phase => cases phase
  | intoSlot wf phase size alignment => cases phase

theorem consumed_raw_handle_cannot_be_result (post : Ledger) :
    ¬ RawIntoSlot typing.layout True OneBackingIssuerWitness.afterRich.ledger ⟨9⟩ ⟨9⟩ typing.node
      (extent context OneBackingIssuerWitness.afterInterpretation) post := by
  intro raw; exact raw.resultFresh raw.sourceClaim.1

end
end NewLang.Adjunct.OneBackingSlotCounterexample
