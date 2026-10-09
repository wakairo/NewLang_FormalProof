import NewLang.Adjunct.Counterexample.FiveRoot
import NewLang.Adjunct.CustodyProofs

/-! Bounded interface experiment for Issue #43. These are conditional frame
lemmas, NOT a new source API or an actual five-root recipient-call certificate.
The existing five-site responsibility ledger is not donor-local availability. -/
namespace NewLang.Adjunct.BComposition
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- A projection of EXISTING holder bookkeeping, not another owner table.
`recipient` labels the destination carrier class, NOT a distinct execution
principal: the old recipient actually stores into a caller-owned local sum. -/
inductive Custodian where | donor | inTransit | recipient | freed
  deriving DecidableEq, Repr

def actor : Custody.Holder → Custodian
  | .packet | .saved | .unpacked => .donor
  | .formal | .displaced => .inTransit
  | .custody => .recipient

def support (s : Custody.State) := s.holders.image actor

/-- The fifth model's original allocation label is an origin label. The old
packet's allocationField is a CURRENT VALUE BINDING and can change on move.
Do not identify them by numeric equality or infer authority from ptr data. -/
structure MatchedB (f : FiveRoot.State) (s : Custody.State) : Prop where
  world : s.heap.world = f.world
  packetWorld : s.packet.world = (f.origin .b).world
  originalWorld : (f.origin .b).world = f.world
  ptr : s.packet.ptr = (f.origin .b).ptr
  region : s.packet.region = (f.origin .b).region
  domain : s.packet.domain = (f.origin .b).domain
  tailLocation : s.heap.roots.tail.location = (f.origin .b).ptr.location
  tailIncarnation : s.heap.roots.tail.incarnation = (f.origin .b).ptr.incarnation
  tailRegion : s.heap.roots.tail.extent.region = (f.origin .b).region
  tailDomain : s.heap.roots.tail.domain = (f.origin .b).domain
  cell : f.cell .b = some s.heap.memory.tail

/-- A real independently proved known-call relation is required. This theorem
never manufactures Applicable from a graph link or from conservation itself. -/
theorem conditional_recipient_transport {g f s r p post body}
    (matched : MatchedB f s) (call : Custody.RecipientCall g body s r p post) :
    MatchedB f post ∧ Custody.WellFormed g post ∧
    support post = {.recipient} ∧
    (∀ role, post.heap.memory.carrier role ≠ some s.packet.allocationField ∧
      post.heap.memory.carrier role ≠ some s.packet.domainField) := by
  have unchanged := Custody.recipient_preserves_original_heap call
  refine ⟨?_,Custody.recipient_preserves_wellFormed call,?_,
    Custody.recipient_consumes_original_donor_bindings call⟩
  · constructor
    · rw [call.2.2]; exact matched.world
    · rw [call.2.2]; exact matched.packetWorld
    · exact matched.originalWorld
    · exact unchanged.2.2.2.2.1.trans matched.ptr
    · exact unchanged.2.2.2.2.2.1.trans matched.region
    · exact unchanged.2.2.2.2.2.2.1.trans matched.domain
    · rw [unchanged.1]; exact matched.tailLocation
    · rw [unchanged.1]; exact matched.tailIncarnation
    · rw [unchanged.1]; exact matched.tailRegion
    · rw [unchanged.1]; exact matched.tailDomain
    · rw [unchanged.2.2.1]; exact matched.cell
  · rw [support,(Custody.recipient_transfers_exactly_one_owner call).1]
    simp [actor]

theorem original_five_frame_under_change (f : FiveRoot.State) (i : FiveRoot.Site)
    (field : FiveRoot.Field) (value) (p : FiveRoot.ChangePlan) :
    (FiveRoot.changePost f i field value p).origin = f.origin ∧
    (FiveRoot.changePost f i field value p).owners = f.owners ∧
    (FiveRoot.changePost f i field value p).claim = f.claim ∧
    (FiveRoot.changePost f i field value p).cell = f.cell := ⟨rfl,rfl,rfl,rfl⟩

theorem matched_B_frames_field_change {f s i field value p} (m : MatchedB f s) :
    MatchedB (FiveRoot.changePost f i field value p) s := by
  exact ⟨m.world,m.packetWorld,m.originalWorld,m.ptr,m.region,m.domain,m.tailLocation,m.tailIncarnation,
    m.tailRegion,m.tailDomain,m.cell⟩

/-- At most one LIVE carrier class is derived from the existing rich owner invariant. -/
theorem rich_live_has_one_custodian {g s} (wf : Custody.WellFormed g s)
    (live : s.heap.memory.tail.phase = .typed) :
    ∃ h, support s = {h} ∧ h ≠ .freed := by
  rcases wf.cover live with ⟨h,only⟩
  refine ⟨actor h,?_,?_⟩
  · simp [support,only]
  · cases h <;> decide

theorem rich_freed_has_no_custodian {g s} (wf : Custody.WellFormed g s)
    (freed : s.heap.memory.tail.phase = .released) : support s = ∅ := by
  simp [support,wf.released freed]

/-- Dropping B's entries from the five-site ledger is NOT a sound donor cut.
That ledger requires world-wide responsibility for every still-live root. -/
theorem deleting_live_B_owners_breaks_five_invariant {f : FiveRoot.State}
    (live : FiveRoot.Typed f .b) (empty : f.owners .b = []) : ¬ FiveRoot.WellFormed f := by
  intro wf
  rcases live with ⟨c,cell,typed⟩
  have own := (wf.memory.present .b c cell).2.1
  rw [empty] at own
  simp [FiveRoot.expectedOwners,typed] at own

/-- Conversely the OLD five-root CanEnd relation has no caller/custodian input.
Keeping its ledger cannot prove that the donor lost availability after a call. -/
theorem field_changes_do_not_revoke_old_end_permission {f i field value p d}
    (can : FiveRoot.CanEnd f .b d)
    (guard : FiveRoot.EndGuard (FiveRoot.changePost f i field value p) .b) :
    FiveRoot.CanEnd (FiveRoot.changePost f i field value p) .b d :=
  ⟨can.1,can.2.1,guard⟩

/-- A distinct independent receiver cannot reuse this closed terminal relation
when its original head projection has already been released. -/
theorem legacy_entry_requires_live_head {c s args}
    (entry : KnownCall.RequiredAtEntry c s args) : s.head.phase = .typed := entry.headLive

theorem legacy_call_rejects_released_head {g c s args a d post}
    (ended : s.head.phase = .released) : ¬ KnownCall.Call g c s args a d post := by
  intro call
  have live := call.2.2.1.headLive
  rw [ended] at live; cases live

theorem rich_terminal_rejects_released_head {g s a d}
    (ended : s.heap.memory.head.phase = .released) : ¬ Custody.TerminalApplicable g s a d := by
  intro entry
  exact legacy_call_rejects_released_head ended entry.base.2.2.2.2.1

/-- Packet identity and holder uniqueness alone cannot remove a call premise. -/
theorem approved_head_cannot_be_rebased {g s : _} (_wf : Custody.WellFormed g s)
    (other : KnownCall.Context) (changed : other.head.location ≠ s.approved.roots.head.location) :
    ¬ Custody.WellFormed g {s with heap := {s.heap with roots := other}} := by
  intro rebased
  exact changed (congrArg (fun c : KnownCall.Context => c.head.location) rebased.roots)

/-- The accepted recipient's destination remains CALLER-owned after unit return.
Renaming its holder "recipient" cannot establish an independent principal. -/
theorem accepted_recipient_preserves_caller_owned_destination {g body s r p post}
    (call : Custody.RecipientCall g body s r p post) :
    post.container = s.container ∧ post.container.callerOwned = true := by
  have unchanged := Custody.recipient_preserves_original_heap call
  refine ⟨unchanged.2.2.2.1,?_⟩
  rw [unchanged.2.2.2.1]
  exact call.2.1.sink.2.2.1

theorem receiver_owned_sink_has_no_existing_applicability {g s r p}
    (receiverOwned : s.container.callerOwned = false) : ¬ Custody.Applicable g s r p := by
  intro entry
  have caller := entry.sink.2.2.1
  rw [receiverOwned] at caller; cases caller

end
end NewLang.Adjunct.BComposition
