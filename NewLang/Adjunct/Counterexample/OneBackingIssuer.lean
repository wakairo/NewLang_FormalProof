import NewLang.Adjunct.OneBackingIssuerWitness

namespace NewLang.Adjunct.OneBackingIssuerCounterexample
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource OneBackingIssuerWitness
noncomputable section

/-- Actually copy the new opaque A into a second available placement. Rich
byte accounting is unchanged and cannot detect this source ownership error. -/
def duplicateAllocation : Source :=
  {afterSource with current := insert (1004,.temporary 1004) afterSource.current}

theorem duplicate_allocation_rejected_while_rich_wf :
    ¬ SourceWF duplicateAllocation ∧ WellFormed afterGeometry layout afterRich := by
  constructor
  · intro wf
    have eq := wf.unique 1004 (.temporary 1004) (.allocationMember 1006)
      (by simp [duplicateAllocation])
      (by simp [duplicateAllocation,afterSource,somePost,freshGrant,Grant.edges,beforeSource])
    cases eq
  · exact concrete_some_simulation.2.2.2

def lostAllocation : Source :=
  {afterSource with current := afterSource.current.erase (1004,.allocationMember 1006)}

theorem lost_original_A_rejected_while_rich_wf :
    ¬ SourceWF lostAllocation ∧ WellFormed afterGeometry layout afterRich := by
  constructor
  · intro wf
    have present : (1004,.allocationMember 1006) ∈ lostAllocation.current := by
      rw [wf.currentExact]
      simp [lostAllocation,afterSource,somePost,freshGrant,Grant.edges,beforeSource]
    simp [lostAllocation] at present
  · exact concrete_some_simulation.2.2.2

/-- Actually put the OLD A value ID in B's member placement, while it is still
held by C. The rich state itself remains untouched. -/
def transplantOldA : Source :=
  {afterSource with
    current := insert (1000,.allocationMember 1006)
      (afterSource.current.erase (1004,.allocationMember 1006))}

theorem transplanted_old_A_current_owner_rejected : ¬ SourceWF transplantOldA := by
  intro wf
  have bad := wf.unique 1000 (.allocationMember 1006) (.allocationMember 1002)
    (by simp [transplantOldA])
    (by simp [transplantOldA,afterSource,somePost,freshGrant,Grant.edges,beforeSource,oldGrant])
  simp at bad

/-- A distinct new value ID is also forbidden from cloning the SAME original R. -/
def clonedOriginGrant : Grant := {freshGrant target beforeSource ok with base := 2000}
def clonedOrigin : Source :=
  {afterSource with
    nextValue := 2004
    grants := insert clonedOriginGrant afterSource.grants
    current := clonedOriginGrant.edges ∪ afterSource.current}

theorem cloned_original_A_identity_rejected : ¬ SourceWF clonedOrigin := by
  intro wf
  have bad := wf.regionUnique clonedOriginGrant (by simp [clonedOrigin])
    (freshGrant target beforeSource ok) (by simp [clonedOrigin,afterSource,somePost]) rfl
  have bad := congrArg Grant.base bad
  simp [clonedOriginGrant,freshGrant,beforeSource] at bad

def wrongOldAllocation : Interpretation :=
  {afterInterpretation with allocation := fun v => if v = 1004 then some ⟨0⟩ else afterInterpretation.allocation v}

theorem old_A_C_cannot_issue_new_B :
    ¬ Refines afterSource afterGeometry afterRich wrongOldAllocation := by
  intro ref
  have fact := ref.allocationOrigin (freshGrant target beforeSource ok)
    (Finset.mem_insert_self _ _)
  simp [wrongOldAllocation,afterInterpretation,interpretationPost,beforeSource,freshGrant,supply] at fact

/-- A second ghost claim claims precisely the bytes already owned by raw_B. -/
def duplicateRaw : F1.Occupancy.State :=
  {afterRich with ledger := {afterRich.ledger with
    active := insert ⟨10⟩ afterRich.ledger.active
    claim := fun id => if id = ⟨10⟩ then .storage (OneBackingIssuerRich.extent supply)
      else afterRich.ledger.claim id}}

theorem duplicate_original_raw_rejected : ¬ WellFormed afterGeometry layout duplicateRaw := by
  intro wf
  apply nonempty_claim_cannot_be_covered_twice wf.accounting
    (a := ⟨9⟩) (b := ⟨10⟩)
  · simp [duplicateRaw,afterRich,OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,supply]
  · simp [duplicateRaw]
  · decide
  · simp [duplicateRaw,afterRich,OneBackingIssuerRich.post,OneBackingIssuerRich.ledger,supply]

/-- Keep all scope, backing, A and member moves but silently lose the final byte. -/
def truncatedRaw : F1.Occupancy.State :=
  {afterRich with
    ledger := {afterRich.ledger with
      claim := fun id =>
        if id = ⟨9⟩ then
          Claim.storage ⟨⟨7⟩,⟨0,23⟩⟩
        else afterRich.ledger.claim id}}

theorem truncated_n_minus_one_rejected_by_refinement :
    ¬ Refines afterSource afterGeometry truncatedRaw afterInterpretation := by
  intro ref
  have full := ref.fullRaw (freshGrant target beforeSource ok) (Finset.mem_insert_self _ _)
  have eq := full.2
  simp [truncatedRaw,afterInterpretation,interpretationPost,freshGrant,beforeSource,supply,target] at eq

theorem truncated_n_minus_one_rejected_by_accounting :
    ¬ WellFormed afterGeometry layout truncatedRaw := by
  intro wf
  have absent : (⟨123⟩ : AbstractByteId) ∉ TotalFootprint afterGeometry truncatedRaw.ledger := by decide
  have present : (⟨123⟩ : AbstractByteId) ∈ ExpectedFootprint truncatedRaw.flat.physical truncatedRaw.ledger := by decide
  exact absent (wf.accounting.coverage.symm ▸ present)

/-- The accepted 3+1 partition is rich WF, yet NO active handle is one full raw.
This is actual accepted RawSplit, not a stipulated malformed partition. -/
theorem accepted_three_plus_one_is_not_one_full_storage :
    WellFormed F1.Occupancy.Counterexample.geometry F1.Occupancy.Counterexample.layout
      ⟨F1.Occupancy.Counterexample.rawState.flat,OneBackingIssuerBoundary.lastByteLedger⟩ ∧
    ¬ ∃ id, Has OneBackingIssuerBoundary.lastByteLedger id
      (.storage F1.Occupancy.Counterexample.full) := by
  constructor
  · exact OneBackingIssuerBoundary.last_byte_split_is_rich_wellFormed
  · rintro ⟨id,active,claim⟩
    simp only [OneBackingIssuerBoundary.lastByteLedger,splitCandidate,
      F1.Occupancy.Counterexample.rawLedger] at active
    simp at active
    rcases active with rfl | rfl <;>
      simp [OneBackingIssuerBoundary.lastByteLedger,splitCandidate,
        F1.Occupancy.Counterexample.cid,F1.Occupancy.Counterexample.full,
        Extent.left,Extent.right,Range.left,Range.right] at claim

/-- Retired R=200 is absent from the live world, so a rich resource supply by
itself permits it; nominal lineage history separately rejects stale reuse. -/
def staleSupply : OneBackingIssuerRich.Supply beforeGeometry beforeRich :=
  {supply with region := ⟨200⟩,freshRegion := by simp [beforeRich,oneRaw]}

theorem stale_semantic_R_rejected_despite_live_freshness :
    staleSupply.region ∉ beforeRich.flat.physical.world.liveRegions ∧
    staleSupply.region ∈ beforeInterpretation.usedRegions ∧
    ¬ Refines afterSource (OneBackingIssuerRich.geometry staleSupply)
      (OneBackingIssuerRich.post staleSupply)
      (interpretationPost staleSupply beforeSource beforeInterpretation) := by
  refine ⟨staleSupply.freshRegion,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨0,by decide,rfl⟩
  · intro ref
    have bad := ref.lineageUnique 0 (by decide) 41 (by decide) (by
      simp [interpretationPost,staleSupply,beforeSource,beforeInterpretation])
    omega

def ghostNoneInterpretation : Interpretation :=
  {beforeInterpretation with allocation := fun v => if v = 1004 then some ⟨7⟩ else beforeInterpretation.allocation v}

theorem none_ghost_Allocation_rejected_by_exact_inventory :
    ¬ Refines beforeSource beforeGeometry beforeRich ghostNoneInterpretation := by
  intro ref
  have bad := (ref.allocationInventory 1004).mp ⟨⟨7⟩,by simp [ghostNoneInterpretation]⟩
  simp [beforeSource,oldGrant] at bad

theorem none_ghost_Some_and_backing_rejected_by_event :
    ¬ IssuerEvent target beforeSource beforeGeometry beforeRich beforeInterpretation .none
      afterSource afterGeometry afterRich afterInterpretation := by
  intro event
  have eq := (every_none_event_is_full_identity event).1
  have bad := congrArg Source.nextRegion eq
  simp [afterSource,somePost,beforeSource] at bad

def earlyTypedDomain : Source := {afterSource with extras := {.typedRoot,.domain}}

theorem early_typed_root_and_domain_rejected : ¬ SourceWF earlyTypedDomain := by
  intro wf
  have bad := wf.noEarly
  simp [earlyTypedDomain] at bad

/-- An independently fabricated live Domain also fails actual accepted F0 WF. -/
def earlyRichDomain : F0.State := {F0.State.empty with liveDomains := {⟨0⟩}}

theorem fabricated_rich_domain_rejected : ¬ F0.WellFormed earlyRichDomain := by
  intro wf
  have bad := (wf.domainCarrierCoherent ⟨0⟩).mp (by simp [earlyRichDomain])
  simp [earlyRichDomain,F0.State.empty] at bad

end
end NewLang.Adjunct.OneBackingIssuerCounterexample
