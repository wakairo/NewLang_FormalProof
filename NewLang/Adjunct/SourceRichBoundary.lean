import NewLang.F1.Occupancy.Counterexample.Cycle
import NewLang.F1.FixedLifetime
import NewLang.Adjunct.KnownCallProofs

/-! Issue #49: accepted-rich boundary lemmas and discriminators, NOT a source
evaluator or OneBacking/Allocation refinement. No F47 packet projection is used.
The lifecycle premises are ACTUAL accepted rich constructors; deriving them
from the frozen experimental source remains an explicit missing interface. -/
namespace NewLang.Adjunct.SourceRichBoundary
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Starting with an actual raw claim conversion and rich initialization derives
the heap root, governing D and physical R. It does NOT derive an Allocation
value or full backing range: neither is an input/output of RawInitialize. -/
theorem initialize_derives_root_domain_region
    {g : Geometry} {layout : Layout} {sites : RootSiteLayout} {aligned ci tc : Prop}
    {raw : Ledger} {slot live : F1.Occupancy.State}
    {rawId slotId rootId : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {pkg : PackageId} {d : DomainId}
    {inc : IncarnationId} {vf : ValueFactId} {access : Evidence}
    (convert : RawIntoSlot layout aligned raw rawId slotId t e slot.ledger)
    (start : F1.Occupancy.RawInitialize g sites ci tc slot slotId rootId t e
      l pkg d inc vf access live) :
    Has raw rawId (.storage e) ∧
    Has live.ledger rootId (.root t l e) ∧
    live.flat.semantic.occupancy l = .live (initializeRoot sites l pkg d inc vf) ∧
    Governs live.flat.semantic inc d ∧
    CurrentAccessPtr live.flat (initializePtr l inc access) ∧
    live.flat.physical.placement l = some (e.placement g) ∧ access.region = e.region := by
  have placement := initialize_consumes_slot_and_preserves_exact_responsibility start
  exact ⟨convert.sourceClaim,placement.2.1,start.backing.semantic.target_after,
    (F0.initialize_creates_governing_relation start.backing.semantic).1,
    F1.Backing.initialize_produces_current_ptr start.backing,placement.2.2,start.backing.region.symm⟩

/-- No Matched/CanEnd triple assumption: equality follows from two actual
constructors naming the same current root claim and location. Local value
placement incarnation is deliberately not equated with heap incarnation. -/
theorem destroy_recovers_exact_initialized_root
    {g : Geometry} {sites : RootSiteLayout} {ci tc ce : Prop}
    {slot live dead : F1.Occupancy.State}
    {slotId rootId emptyId : ClaimId} {t : TypeId} {e f : Extent}
    {l : RootLocationId} {pkg : PackageId} {d ending : DomainId}
    {inc : IncarnationId} {vf : ValueFactId} {access : Evidence}
    {root : F0.LiveRoot} {ptr : AccessPtr}
    (start : F1.Occupancy.RawInitialize g sites ci tc slot slotId rootId t e
      l pkg d inc vf access live)
    (finish : F1.Occupancy.RawDestroy ce live rootId emptyId t f l root ending ptr dead) :
    f = e ∧ root = initializeRoot sites l pkg d inc vf ∧ ending = d ∧
    ptr.token = ⟨l,inc⟩ ∧ Has dead.ledger emptyId (.slot t e) ∧
    dead.flat.physical.placement l = none := by
  have produced := (initialize_consumes_slot_and_preserves_exact_responsibility start).2.1
  have eq : f = e := (Claim.root.inj (finish.sourceClaim.2.symm.trans produced.2)).2.2
  have rootEq : root = initializeRoot sites l pkg d inc vf :=
    Occupancy.live.inj (finish.backing.semantic.target_live.symm.trans start.backing.semantic.target_after)
  have ended := destroy_consumes_root_and_returns_same_slot finish
  refine ⟨eq,rootEq,?_,?_,?_,ended.2.2⟩
  · simpa [rootEq,initializeRoot] using finish.backing.semantic.domain_matches
  · simpa [rootEq,initializeRoot] using finish.backing.token
  · simpa [eq] using ended.2.1

/-- Actual destroy and erase preserve exactly the supplied extent, byte
responsibility and backing world. Fullness is not silently added. -/
theorem destroy_erase_preserves_exact_claim
    {g : Geometry} {ce : Prop} {live dead : F1.Occupancy.State} {raw : Ledger}
    {rootId slotId rawId : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {root : F0.LiveRoot} {d : DomainId} {ptr : AccessPtr}
    (finish : F1.Occupancy.RawDestroy ce live rootId slotId t e l root d ptr dead)
    (erase : RawEraseSlot dead.ledger slotId rawId t e raw) :
    Has raw rawId (.storage e) ∧
    TotalFootprint g raw = TotalFootprint g live.ledger ∧
    dead.flat.physical.world = live.flat.physical.world ∧
    rootId ∉ dead.ledger.active ∧ slotId ∉ raw.active := by
  have ended := destroy_consumes_root_and_returns_same_slot finish
  have erased := erase_slot_consumes_empty_exact_range erase
  exact ⟨erased.2,(erase_slot_conserves_all_byte_responsibility g erase).trans
    (destroy_conserves_byte_responsibility finish),(destroy_does_not_end_backing finish).1,
    ended.1,erased.1⟩

/-- Fullness is an original grant obligation. Once actually supplied, rich
accounting excludes every other claim in the same region. No Allocation value
or deallocation constructor is thereby created. -/
theorem full_recovery_excludes_other_claims
    {g : Geometry} {layout : Layout} {ce : Prop}
    {live dead : F1.Occupancy.State} {raw : Ledger}
    {rootId slotId rawId : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {root : F0.LiveRoot} {d : DomainId} {ptr : AccessPtr}
    (finish : F1.Occupancy.DestroyStep g layout ce live rootId slotId t e l root d ptr dead)
    (erase : RawEraseSlot dead.ledger slotId rawId t e raw)
    (originalFull : e.range = ⟨0,g.capacity e.region⟩) :
    Accounting g layout (FlatLive dead.flat.semantic) dead.flat.physical raw ∧
    ∀ other ∈ raw.active, other ≠ rawId → (raw.claim other).extent.region ≠ e.region := by
  have accounting := (erase_slot_step_of_raw finish.2.2.accounting erase).2.2
  have hasRaw := (erase_slot_consumes_empty_exact_range erase).2
  refine ⟨accounting,?_⟩
  intro other active different same
  exact full_region_storage_excludes_outstanding_subclaim accounting hasRaw originalFull active different same

/-- Wrong D is rejected by the ACCEPTED rich destroy constructor itself. -/
theorem wrong_governing_domain_rejected
    {ce : Prop} {s post : F1.Occupancy.State} {source result : ClaimId}
    {t : TypeId} {e : Extent} {l : RootLocationId} {root : F0.LiveRoot}
    {d : DomainId} {ptr : AccessPtr} (wrong : d ≠ root.governing) :
    ¬ F1.Occupancy.RawDestroy ce s source result t e l root d ptr post :=
  fun h => wrong h.backing.semantic.domain_matches

/-- Wrong Allocation REGION rejects in the accepted KnownCall adjunct once
the argument's region has actually been established. Its separate region and
binding fields do not establish that correlation from source by themselves. -/
theorem known_call_rejects_wrong_allocation_region
    {c : KnownCall.Context} {s : KnownCall.State} {args : KnownCall.Arguments}
    (wrong : args.allocationRegion ≠ c.tail.extent.region) :
    ¬ KnownCall.RequiredAtEntry c s args :=
  KnownCall.entry_rejects_wrong_allocation_region wrong

/-- Rich F1 current-state WF has no interpretation of opaque installed content.
This is a discriminator against using WF ALONE to infer Allocation provenance,
not an allowed source mutation or counterexample to value-transfer semantics. -/
theorem current_wellFormed_does_not_interpret_installed_content
    {s : F1.CurrentState} (wf : F1.CurrentWellFormed s)
    (content : RootLocationId → PlaceId → Nat) :
    F1.CurrentWellFormed {s with content := content} :=
  ⟨wf.structural,wf.looseStructured,wf.rootCapability⟩

/-- Actual claim accounting does reject two distinct active root claims for
the same nonempty extent. It does not interpret a second opaque source packet
as such a duplicate claim without the missing constituent refinement. -/
theorem accounting_rejects_duplicate_root_claim
    {g : Geometry} {layout : Layout} {s : F1.Occupancy.State}
    (wf : F1.Occupancy.WellFormed g layout s)
    {a b : ClaimId} {t : TypeId} {l : RootLocationId} {e : Extent}
    (first : Has s.ledger a (.root t l e))
    (second : Has s.ledger b (.root t l e)) (different : a ≠ b) : False := by
  apply nonempty_claim_cannot_be_covered_twice wf.accounting first.1 second.1 different
  rw [first.2,second.2]

/-- F0 initialization requires an ALREADY LIVE D; it cannot simulate the
source lifetime_domain() grant from empty. No domain-creation rule is invented. -/
theorem initialization_does_not_issue_a_domain_from_empty
    {g : Geometry} {sites : RootSiteLayout} {ci tc : Prop}
    {s post : F1.Occupancy.State} {source result : ClaimId} {t : TypeId} {e : Extent}
    {l : RootLocationId} {pkg : PackageId} {d : DomainId}
    {inc : IncarnationId} {vf : ValueFactId} {access : Evidence}
    (empty : s.flat.semantic = F0.State.empty) :
    ¬ F1.Occupancy.RawInitialize g sites ci tc s source result t e l pkg d inc vf access post := by
  intro raw
  have live := raw.backing.semantic.domain_live
  rw [empty] at live
  exact Finset.notMem_empty d live

/-- Taking a whole local value returns its EXACT opaque contents/dependencies
and leaves all modeled domain-carrier identities intact. Mapping them to actual
Allocation/Domain constituents requires a separate interpreter/refinement. -/
theorem rich_whole_take_preserves_value_and_domain_carriers
    {ce read : Prop} {s post : F1.CurrentState} {l : RootLocationId} {d : DomainId}
    (take : F1.FixedLifetime.RawEndRoot ce read s l d true post) :
    post.carried (s.base.root l).package =
      some (F1.extractValue s (F1.FixedLifetime.rootTarget s l)) ∧
    post.base.domainValueCarrier = s.base.domainValueCarrier :=
  ⟨(F1.FixedLifetime.take_returns_exact_value take).2.1,
    (F1.FixedLifetime.end_preserves_domains take).2⟩

/-- Concrete accepted-rich control: a fully valid typed lifecycle in a half
region returns HALF raw Storage; the other half remains independently owned.
Thus current typed root + successful destroy/erase does not imply full raw. -/
theorem accepted_typed_cycle_does_not_imply_full_raw :
    F1.Occupancy.DestroyStep Counterexample.geometry Counterexample.layout True
      Counterexample.restarted (Counterexample.cid 6) (Counterexample.cid 7)
      Counterexample.ty Counterexample.left ⟨0⟩ (Counterexample.root 2) ⟨0⟩
      Counterexample.secondPtr Counterexample.ended ∧
    EraseSlotStep Counterexample.geometry Counterexample.layout
      (FlatLive Counterexample.ended.flat.semantic) Counterexample.ended.flat.physical
      Counterexample.endLedger (Counterexample.cid 7) (Counterexample.cid 8)
      Counterexample.ty Counterexample.left Counterexample.erasedLedger ∧
    Has Counterexample.erasedLedger (Counterexample.cid 8) (.storage Counterexample.left) ∧
    Counterexample.left.range ≠
      ⟨0,Counterexample.geometry.capacity Counterexample.left.region⟩ ∧
    Has Counterexample.erasedLedger (Counterexample.cid 20) (.storage Counterexample.right) := by
  refine ⟨Counterexample.destroy_is_legal,Counterexample.erase_slot_is_legal,
    (erase_slot_consumes_empty_exact_range Counterexample.erase_slot_is_legal.2.1).2,
    by decide,?_⟩
  exact ⟨by decide,by rfl⟩

end
end NewLang.Adjunct.SourceRichBoundary

