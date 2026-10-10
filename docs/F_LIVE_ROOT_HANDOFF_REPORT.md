# Original five-root LiveRoot handoff: bounded formal interface findings

Track: F — FormalProof Issue #47.

**HOLD.** The proposed whole-value path has a constructive finite conservation
projection. The accepted five-root heap also admits the exact requested physical
write/cleanup sequence. Neither establishes that a source `TreeTwo` carries the
original Allocation/Domain semantic values through the proposed named calls.
The smallest critical missing interface is the refinement from current aggregate
constituents and consuming bindings to original world-qualified p/O/R/A/D
authority, including borrowed-domain-field conflicts and per-root terminal calls.
There is no demonstrated contradiction in canonical core semantics.

## Fixed authority and scope

- FormalProof base/main: `fcf24840b5f6799a431ad5d3fa4fedcec5d4291c`.
- Compiler main: `b75baea96a644e68634baee383299b66981b3c62`.
- `docs/reference/CURRENT_SPEC.md`: **Draft 17.30**. Its five-root §3.2b
  source admission remains PRE-detach only; §18.1a/b/c remains a separate
  bounded two-root profile.
- Read Issue #47, M #270 report `6092413576`, Coordination adjudication
  `6092438428`, gate #268 and its authorization `6092454418`, F #43 and its
  accepted report/model. Draft §§3.2b,10–14/14.5,16.1,17.4,18.1a–c,18.6,
  26–27 were consulted against the fixed Compiler checkout.
- Historical source-selection review is N/A for this isolated non-selecting
  Adjunct experiment. It remains mandatory before selecting any source proposal.
- No accepted theorem meaning, canonical source, compiler implementation,
  toolchain, whitelist, CI configuration or product gate was changed. The PR
  stays OPEN/unmerged and Issue #47 remains OPEN for Coordination.

## Three levels of evidence

1. **Accepted kernel/adjunct evidence.** Original five allocation snapshots,
   scoped field writes and their Change/Reset guards, original typed-root/slot/raw
   cleanup, and the old two-root KnownCall relation are reused unmodified.
2. **New finite conditional projection.** `LiveRootHandoff.lean` defines whole
   `Four`, `Split`, `Three`, `Two` values and eight current binding positions.
   `Ticket` is an alias of the accepted original `Origin` descriptor, not a
   language constructor granting authority. `Detach`, `Open`, `Enter`, `Return`
   check actual input bindings and vacant output positions. Their deterministic
   operations consume old inputs and construct outputs. Conservation is proved
   for arbitrary tickets and all residual frame values; it is not a post-WF or
   unique-ledger premise. The initial five-ticket count is computed from the
   original five descriptors. `LocalCanEnd` is an explicitly proposed membership
   adapter, **not an accepted source release judgment**.
3. **Missing accepted rich/source refinement.** The projection does not implement
   F1 structural aggregate construction/destruction, fresh local incarnations,
   current Allocation/Domain field carriers, declaration checking, loan inference
   or source normal-exit checking. Its `none` slots do not distinguish untouched
   and consumed historical bindings; only the fixed single trace is claimed.
   There is no actual NewLang source evaluation or five-root adopter-call
   certificate. These limitations prevent a finite-proof/source PASS.

F0 `ValuePackage` explicitly omits payload/authority algebra. F1
`StructuredValue` carries opaque content tokens and exact dependency fragments;
their mere existence does not supply an interpretation of each new ticket's
Allocation/Domain constituent. F0 package carrier uniqueness and
`domainValueCarrier` coherence cannot by themselves prove that the two original
authority constituents occur inside this particular returned `TreeTwo`.

## F43-1/2/3: what was repaired, and what remains missing

| F43 blocker | Accepted evidence | New checked conditional result | Missing adapter / countermodel |
| --- | --- | --- | --- |
| F43-1 world responsibility versus current local value | `FiveRoot.allocation_has_one_original_pair`; F0 domain carrier transfer/coherence; F43 `deleting_live_B_owners_breaks_five_invariant` | Four→Split→Three+ticket→callee parameters→one Two preserves a multiset of the exact originals. At return each original appears once; old donor/packet/formal slots are consumed. | No accepted relation maps these slots/constituents to the actual rich current carriers. `global_canEnd_is_not_local_availability` keeps accepted B End permission while the chosen donor is consumed. `local_entry_alone_does_not_prove_unique_custody` admits a duplicate ghost holder to local entry checks. |
| F43-2 caller Option versus actual dst+B receiving value | Existing Custody recipient preserves its caller-owned Option; this theorem remains unchanged | `named_return_has_same_dst_and_B` derives one Two containing exact K_dst and K_B from consumed inputs; conservation comes from operations. `H0_conserves_inventory_but_fails_receiver_ownership` has a separate caller B packet, all five accounted, and no B authority inside the dst-only receiver. | The new aggregate/call result is a projection, not an accepted Custody/known-attach application. Successful field writes do not constrain the unused Allocation field: `field_body_does_not_check_allocation_constituent`. |
| F43-3 terminal after original A is dead | Actual FiveRoot Cleanup admits A,C,src then B,dst; exact original full extents are retained | A NEW independently checked dst/B KnownCall context has an actual accepted `KnownCall.Call` witness for B with original A already released. It matches actual before/after cells, proves full-B recovery and no callee residue/double free. | That view's current bindings are projected manually, not obtained from TreeTwo source consumption. Reversing it to B/dst for the second call fails because B is now released (`second_old_call_is_not_finish_two`). Need the distinct source-checked `finish_root`/`finish_two` whole-call interface; primitive dst cleanup alone is insufficient. |

`LiveRootReceiverView.lean` constructs a **new** context and proves
`ContextValid`, `WellFormed`, `RequiredAtEntry`, fresh parameter and survivor
guards. It never mutates/rebases `Custody.approved`, and the old A-head call still
fails. This shows that the A-head blocker is interface-specific, not a core
impossibility. The witness is an accepted **KnownCall adjunct** application,
not a complete F1 current/occupancy/source refinement or an adopter proof.

## Allocation constituent inference: concrete missing interface

The adopter body reads p and loans D, updates `dst.child` and `B.prev`, and returns
the untouched Allocation constituent. The accepted B write relation continues
to hold for a packet descriptor with original p_B and D_B but C's Allocation
label. `forgedBRef` is the identical authentic B ref: field applicability checks
world/p/D/liveness/access, not an unused Allocation argument.

This is **not** a successful bad NewLang program or memory-unsafety finding.
An actual B terminal must reject the wrong allocation/region, and construction
of genuine packets in the intended main trace may preserve the right pairing.
However, a claim that the adopter *body alone* infers full p/A/D original matching
needs justification. `Matched` explicitly demands that equality; neither the
nominal type nor the two writes proves it. The missing interface must show how
actual allocation/init packages and whole constructor/result flow retain this
correlation, or explain a separately checked caller requirement. It cannot
silently add a `CarriesLiveH` bit or assume the desired post-state.

## Borrowed domain field and rich predicates

`domainLive_alone_does_not_block_transfer` gives an actual accepted F0 witness
with a surviving DomainLive dependency while the same D moves to another
carrier. This is intentional §14.5 behavior, not a core safety gap:
`RawDomainTransfer.transfer_allowed` abstracts current-value capability conflicts.

`owner_place_loan_blocks_take` uses accepted
`F0.take_rejects_surviving_old_current_dependency`.
`domain_field_loan_blocks_whole_consume` uses accepted
`F1.FixedLifetime.end_rejects_external_ended_fact_dependency`: a capability
depending on the actual tracked domain FIELD current fact blocks ending the
whole owner root. The missing part is generating that dependency and compatible
scope evidence from the proposed `loan_read(ticket@domain)`, and carrying it
through nested whole aggregate use and function entry. Heap `loans` and
DomainLive alone are not that source-place adapter. No ref escape or
write-to-exclusive strengthening is granted by this experiment.

## Exact original five-world ledger

All heap states start at the accepted `wired6`; four checked detach writes and
two checked adoption writes are the unmodified F43 witnesses. Each has an
authentic root-D scoped field ref and fresh field/parent facts and Option
occurrences. Original O/R/A/D/cell/claim identities survive all six. Original C
is the sibling node, never a logical temporary Tree D.

| Checkpoint | Source-current packet projection | Physical original heap / frees |
| --- | --- | --- |
| Initial | Four(src,A,B,C), separate ticket(dst) | Five independent live original roots; six initial writes and dst.child=None |
| Producer return | Split(Three(src,A,C), ticket(B)) | A.next=C, C.prev=A, B.prev=None, B.next=None; all five still live |
| Adopter entry | callee formalRoot(dst), formalChild(B), donor Three | Prior receiver/packet bindings consumed; no sixth allocation |
| Adopter return | one Two(root=dst,child=B), donor Three | dst.child=B, B.prev=B, B.next=None; all five live; callee formals consumed |
| Donor done | one Two(dst,B); donor binding consumed | A(#2),C(#4),src(#1) ended/finalized/freed once; B/dst stay original/live |
| Whole terminal entry | TreeTwo consumed; two ticket formals | A already dead; original B/dst current, scopes closed |
| B terminal done | only dst formal | original B(#3) ended; exact full R_B raw claim recovered; D_B finalized; A_B released once |
| Receiver terminal done | empty inventory; both formals consumed | original dst(#5) similarly freed; all five original cells released exactly once |

`exact_donor_then_receiver_trace` is actual accepted FiveRoot `ActualCleanup`
in order #2,#4,#1,#3,#5. `finish_B` and `finish_dst` derive applicability from
WellFormed/current typed cells and closed guards. `original_full_raw_B_dst_recovered`
records the same original typed-H→slot→raw claim, and
`exact_five_frees_no_remint` records all original descriptors and exact counts.
This uses `cleanup_available`/`cleanup_preserves_wellFormed` and the accepted
`root_slot_raw_conservation`, not a guessed raw extent. It does **not** supply
the missing actual F1.Occupancy `RawDestroy`/`RawEraseSlot`/Allocation-value
source/call adapter; the rich predicates requiring exact claims and matching
backing/access remain necessary.

## Failure, refusal and error boundary

| Original allocation successes | Packets that can exist | Original free sequence |
| --- | --- | --- |
| 0 | none | none |
| 1 | src | src (#1) |
| 2 | src,A | A,src (#2,#1) |
| 3 | src,A,B | B,A,src (#3,#2,#1) |
| 4 | src,A,B,C | C,B,A,src (#4,#3,#2,#1) |
| 5 accepted | all five, then whole handoff | A,C,src,B,dst (#2,#4,#1,#3,#5) |

`failures_no_unseen_packet` checks membership iff site.code<successes, for all
six outcomes and all five roles. `allocation_failure_exact_frees` reuses the
actual existing failure cleanup witnesses and exact counts. No unseen allocation
grant is forged. The packet list is only an identity projection of these grants.

Before-detach and detached-pre-attach refusal both have actual explicit cleanup
witnesses B,A,C,src,dst (#3,#2,#4,#1,#5), matching M's finish_four/finish_root or
detached finish_root/finish_three/receiver finish_root paths. Each scope is closed
and every original is discharged. Later refusal can consume the sole complete
Two using the same accepted physical terminal sequence and projected disposition.

`ClosedAttach` proves existence and conservation for the fixed two-write
straight-line proposed body and an empty result slot, under checked matched input
and affine entry premises. Its two physical writes are independently established
accepted witnesses. Its only modeled normal result is the complete Two.
This is **conditional projection totality**, not verification that all proposed
source definition/call applicability premises are inferable.

An adapter admitting an arbitrary postconsume bool-only exit is falsified:
`bool_only_postconsume_error_loses_both` removes B/dst from accountability;
`closed_attach_has_no_boolean_error_edge` rejects that output for this closed
body. A future fallible API needs exact typed nonCopy accept/refund of BOTH
originals or retained committed ownership and proven current topology. No
callback/FFI/unwind/GC behavior is modeled or generalized.

## Negative controls and limits

- Consumed donor/holder reuse: rejected by the finite binding relations and
  proposed local guard; the accepted global End relation remains actorless.
- Duplicate original B: local entry alone admits a forged second ghost holder;
  the derived initial inventory and conserving operations do not create one.
  Connecting this to actual nonCopy source carriers is still mandatory.
- H0 unrelated caller packet: five conserved, B available outside Tree B, no
  B ticket inside its complete dst-only owner. It fails H1 even if memory safe.
- Wrong-world and identical-pointer/wrong-original-region packets: rejected by
  `Matched`; wrong Allocation pairing still allows physical field writes and
  exposes the missing original-authority inference. Numeric address is not R/O
  provenance (accepted backing same-address control remains unchanged).
- Active D_B heap loan: accepted End rejects; finite entry alone ignores it.
  Actual borrowed ticket-domain whole transfer remains a missing source adapter.
- Stale Option occurrence and selected old current fact: accepted F43/FiveRoot
  Change/Reset controls remain checked; sibling fields retain their own ProjectionId.
- B double release and legacy terminal after A death: rejected by accepted
  cleanup/KnownCall guards. The new dst/B terminal view does not weaken the old one.
- Skipped B/ticket and postconsume bool error: concrete inventory loss, not a
  complete disposition. Final positive projected normal exit has empty inventory.
- Graph-policy errors remain separable from memory WellFormedness; a dangling
  Copy dst.child after B release is not dereferenced or promoted to owner authority.

These are formal predicates/countermodels, not production static B1–B7 rejection
counts, parser-profile PASSes, emitted C, native cJSON evidence or H2 actor results.

## Explicit unproved external obligations and recommendation

Still required: genuine OneBacking/initialize→current LiveRoot constituent
interpretation; whole construction/destruction/result preservation with fresh
source placements; actual five-world body-sensitive call summaries (especially
unused Allocation matching); domain-field scope/current-fact dependencies and
scope nonescape; per-root finish_root and whole finish_two calls; exact accepted
rich claim/Storage/Allocation release refinement and ordinary nonDiscardable
branch/exit discharge. Platform access/allocator facts remain the existing
explicit boundary, not new semantic authority or custom logic assumptions.

**BLOCK canonical source selection on this evidence.** Return these precise
interfaces to independent Coordination/M. A separately reviewed narrow
Draft17.31 proposal may be considered only after making its inference/refinement
obligations explicit; no broad Owner/Drop/core change is shown necessary. No new
Track is launched. Gate #268 stays OPEN; full original cJSON B native work stays
STOP; H1/North Star PASS/FAIL stays UNDECIDED and old H2 history is preserved.

## Validation

Baseline: `lake build` PASS (797 jobs); `scripts/check-proofs.sh` PASS, 1652
audited declarations. Candidate: `lake build` PASS (800 jobs); `scripts/check-proofs.sh` PASS,
1769 = 1652 retained + 117 new public definitions/theorems. Exact-head GitHub CI
is recorded in the Issue #47 handoff. The audit appends all 117 new public
definitions/theorems, retaining every baseline entry and the unchanged whitelist
`propext`, `Classical.choice`, `Quot.sound`. No project-owned proof placeholder
or custom semantic logic assumption is introduced. Lean 4.34.1 / mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins are unchanged.

The exact audit declaration list follows; the three namespaces correspond to
the model, concrete five-world controls, and independently checked terminal view.

```text
NewLang.Adjunct.LiveRootHandoff.Value.tickets
NewLang.Adjunct.LiveRootHandoff.bindings
NewLang.Adjunct.LiveRootHandoff.inventory
NewLang.Adjunct.LiveRootHandoff.put
NewLang.Adjunct.LiveRootHandoff.detachBody
NewLang.Adjunct.LiveRootHandoff.detachPost
NewLang.Adjunct.LiveRootHandoff.openPost
NewLang.Adjunct.LiveRootHandoff.enterPost
NewLang.Adjunct.LiveRootHandoff.returnPost
NewLang.Adjunct.LiveRootHandoff.Detach
NewLang.Adjunct.LiveRootHandoff.Open
NewLang.Adjunct.LiveRootHandoff.Enter
NewLang.Adjunct.LiveRootHandoff.Return
NewLang.Adjunct.LiveRootHandoff.detach_conserves
NewLang.Adjunct.LiveRootHandoff.open_conserves
NewLang.Adjunct.LiveRootHandoff.enter_conserves
NewLang.Adjunct.LiveRootHandoff.return_conserves
NewLang.Adjunct.LiveRootHandoff.detach_consumes_donor
NewLang.Adjunct.LiveRootHandoff.enter_consumes_both
NewLang.Adjunct.LiveRootHandoff.return_combines_exact_originals
NewLang.Adjunct.LiveRootHandoff.consumed_donor_rejects_detach
NewLang.Adjunct.LiveRootHandoff.consumed_holder_rejects_enter
NewLang.Adjunct.LiveRootHandoff.Matched
NewLang.Adjunct.LiveRootHandoff.matched_wrong_world_rejected
NewLang.Adjunct.LiveRootHandoff.matched_wrong_region_rejected
NewLang.Adjunct.LiveRootHandoff.matched_wrong_allocation_rejected
NewLang.Adjunct.LiveRootHandoff.matched_wrong_domain_rejected
NewLang.Adjunct.LiveRootHandoff.LocalCanEnd
NewLang.Adjunct.LiveRootHandoff.consumed_binding_cannot_end
NewLang.Adjunct.LiveRootHandoff.domainLive_alone_does_not_block_transfer
NewLang.Adjunct.LiveRootHandoff.owner_place_loan_blocks_take
NewLang.Adjunct.LiveRootHandoff.domain_field_loan_blocks_whole_consume
NewLang.Adjunct.LiveRootHandoff.Counterexample.four
NewLang.Adjunct.LiveRootHandoff.Counterexample.initial
NewLang.Adjunct.LiveRootHandoff.Counterexample.splitFrame
NewLang.Adjunct.LiveRootHandoff.Counterexample.openFrame
NewLang.Adjunct.LiveRootHandoff.Counterexample.entered
NewLang.Adjunct.LiveRootHandoff.Counterexample.returned
NewLang.Adjunct.LiveRootHandoff.Counterexample.actual_projection_steps
NewLang.Adjunct.LiveRootHandoff.Counterexample.all_stages_conserve_original_five
NewLang.Adjunct.LiveRootHandoff.Counterexample.each_original_once
NewLang.Adjunct.LiveRootHandoff.Counterexample.each_original_once_at_return
NewLang.Adjunct.LiveRootHandoff.Counterexample.named_return_has_same_dst_and_B
NewLang.Adjunct.LiveRootHandoff.Counterexample.donor_has_no_B_at_return
NewLang.Adjunct.LiveRootHandoff.Counterexample.old_bindings_have_no_local_release
NewLang.Adjunct.LiveRootHandoff.Counterexample.all_five_matched_before_and_after
NewLang.Adjunct.LiveRootHandoff.Counterexample.heap_change_endpoints_and_representative_checks
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterA
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterC
NewLang.Adjunct.LiveRootHandoff.Counterexample.donorDone
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterB
NewLang.Adjunct.LiveRootHandoff.Counterexample.done
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterDonor
NewLang.Adjunct.LiveRootHandoff.Counterexample.terminalEntered
NewLang.Adjunct.LiveRootHandoff.Counterexample.terminalAfterB
NewLang.Adjunct.LiveRootHandoff.Counterexample.terminalDone
NewLang.Adjunct.LiveRootHandoff.Counterexample.finish_A
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterA_wellFormed
NewLang.Adjunct.LiveRootHandoff.Counterexample.finish_C
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterC_wellFormed
NewLang.Adjunct.LiveRootHandoff.Counterexample.finish_src
NewLang.Adjunct.LiveRootHandoff.Counterexample.donorDone_wellFormed
NewLang.Adjunct.LiveRootHandoff.Counterexample.finish_B
NewLang.Adjunct.LiveRootHandoff.Counterexample.afterB_wellFormed
NewLang.Adjunct.LiveRootHandoff.Counterexample.finish_dst
NewLang.Adjunct.LiveRootHandoff.Counterexample.done_wellFormed
NewLang.Adjunct.LiveRootHandoff.Counterexample.exact_donor_then_receiver_trace
NewLang.Adjunct.LiveRootHandoff.Counterexample.after_A_only_TreeTwo_locally_can_end_B_dst
NewLang.Adjunct.LiveRootHandoff.Counterexample.terminal_affine_disposition
NewLang.Adjunct.LiveRootHandoff.Counterexample.terminal_each_formal_matched_at_use
NewLang.Adjunct.LiveRootHandoff.Counterexample.original_full_raw_B_dst_recovered
NewLang.Adjunct.LiveRootHandoff.Counterexample.exact_five_frees_no_remint
NewLang.Adjunct.LiveRootHandoff.Counterexample.primitive_B_double_release_rejected
NewLang.Adjunct.LiveRootHandoff.Counterexample.global_canEnd_is_not_local_availability
NewLang.Adjunct.LiveRootHandoff.Counterexample.allocationPackets
NewLang.Adjunct.LiveRootHandoff.Counterexample.failures_no_unseen_packet
NewLang.Adjunct.LiveRootHandoff.Counterexample.allocation_failure_exact_frees
NewLang.Adjunct.LiveRootHandoff.Counterexample.boolOnlyPost
NewLang.Adjunct.LiveRootHandoff.Counterexample.bool_only_postconsume_error_loses_both
NewLang.Adjunct.LiveRootHandoff.Counterexample.copyOnly
NewLang.Adjunct.LiveRootHandoff.Counterexample.copy_only_receiver_does_not_have_B
NewLang.Adjunct.LiveRootHandoff.Counterexample.unrelatedCallerPacket
NewLang.Adjunct.LiveRootHandoff.Counterexample.H0_conserves_inventory_but_fails_receiver_ownership
NewLang.Adjunct.LiveRootHandoff.Counterexample.wrongWorld
NewLang.Adjunct.LiveRootHandoff.Counterexample.samePtrWrongR
NewLang.Adjunct.LiveRootHandoff.Counterexample.wrong_world_and_same_ptr_wrong_region_rejected
NewLang.Adjunct.LiveRootHandoff.Counterexample.B_absent_from_TreeTwo_is_not_completed
NewLang.Adjunct.LiveRootHandoff.Counterexample.wrongAllocation
NewLang.Adjunct.LiveRootHandoff.Counterexample.forgedBRef
NewLang.Adjunct.LiveRootHandoff.Counterexample.field_body_does_not_check_allocation_constituent
NewLang.Adjunct.LiveRootHandoff.Counterexample.duplicateFrame
NewLang.Adjunct.LiveRootHandoff.Counterexample.local_entry_alone_does_not_prove_unique_custody
NewLang.Adjunct.LiveRootHandoff.Counterexample.entry_projection_alone_does_not_check_heap_loan
NewLang.Adjunct.LiveRootHandoff.Counterexample.ClosedAttach
NewLang.Adjunct.LiveRootHandoff.Counterexample.closed_attach_constructive_totality
NewLang.Adjunct.LiveRootHandoff.Counterexample.actual_closed_attach
NewLang.Adjunct.LiveRootHandoff.Counterexample.closed_attach_has_no_boolean_error_edge
NewLang.Adjunct.LiveRootHandoff.Counterexample.pre_detach_and_detached_refusal_exact_cleanup
NewLang.Adjunct.LiveRootHandoff.ReceiverView.root
NewLang.Adjunct.LiveRootHandoff.ReceiverView.roots
NewLang.Adjunct.LiveRootHandoff.ReceiverView.before
NewLang.Adjunct.LiveRootHandoff.ReceiverView.args
NewLang.Adjunct.LiveRootHandoff.ReceiverView.post
NewLang.Adjunct.LiveRootHandoff.ReceiverView.exact_actual_original_cells
NewLang.Adjunct.LiveRootHandoff.ReceiverView.new_context_valid
NewLang.Adjunct.LiveRootHandoff.ReceiverView.before_wellFormed
NewLang.Adjunct.LiveRootHandoff.ReceiverView.new_entry_proved
NewLang.Adjunct.LiveRootHandoff.ReceiverView.actual_B_known_call_after_A_dead
NewLang.Adjunct.LiveRootHandoff.ReceiverView.post_wellFormed
NewLang.Adjunct.LiveRootHandoff.ReceiverView.exact_actual_post_cells
NewLang.Adjunct.LiveRootHandoff.ReceiverView.terminal_recovers_same_full_B
NewLang.Adjunct.LiveRootHandoff.ReceiverView.new_call_no_callee_packet_residue
NewLang.Adjunct.LiveRootHandoff.ReceiverView.new_call_B_cannot_double_release
NewLang.Adjunct.LiveRootHandoff.ReceiverView.old_A_head_still_blocks
NewLang.Adjunct.LiveRootHandoff.ReceiverView.dstRoots
NewLang.Adjunct.LiveRootHandoff.ReceiverView.dstBefore
NewLang.Adjunct.LiveRootHandoff.ReceiverView.second_old_call_is_not_finish_two
```

F CJSON-B-STATE-1 ORIGINAL LIVE-ROOT HANDOFF: HOLD — CRITICAL ACCEPTED RICH/CALL INTERFACE UNPROVED
