# Five-root original-B custody composition: bounded interface experiment

Track: F — Issue #43.

**Disposition: HOLD — minimal formal adapter / countermodel.** This is evidence
about the current formal interfaces, not a claim that Draft 17.30 forbids a
correct program or requires a new language mechanism.

## Authority and process

- FormalProof base main: `608d99505737e011006f902768478430f32c83b8`.
- Compiler main: `d8765a5ae11919d3076cec0d1432973a0f18fdcd`.
- Compiler `CURRENT_SPEC.md`: Draft 17.30; its development process and Design
  Decision Procedure / DI-009–014 were consulted.
- The historical design-selection gate is not invoked to select new syntax,
  API, or semantics: this is a faithful finite interface experiment. The
  existing two-root and five-root evidence remains distinct.
- No dependency on unmerged P/M work; no canonical, Compiler, CI, README,
  toolchain, manifest, or existing theorem changes.

## Small model and exact hypotheses

`NewLang/Adjunct/BComposition.lean` imports the accepted FiveRoot and Custody
models. `MatchedB` correlates world, original world, packet world, pointer O,
BackingRegion R, LifetimeDomain D, tail root identity, and actual B cell.
Original Allocation labels remain in the unchanged FiveRoot origin descriptor;
current packet Allocation/Domain **value bindings** are separately tracked by
Custody and can change on transfer. Numeric equality of these different kinds
of identity is not an ownership proof.

`Custodian` is proof-only bookkeeping, projected from existing `Holder` support.
Its `recipient` constructor denotes the custody carrier class; it deliberately
does not pretend that this is a distinct execution principal.

`conditional_recipient_transport` requires BOTH `MatchedB f s` and an
independently established **actual** `Custody.RecipientCall`. From those it
proves the original-B match is preserved, rich WellFormedness, singleton custody
support, and removal of old donor value bindings from all current carriers.
It does not assume its own conservation conclusion or post-WellFormedness.
**No actual matched five-root recipient-call witness is claimed.**

`original_five_frame_under_change` is a quantified frame lemma for every field
change, not a five-row fixture. It preserves all original descriptors, world
responsibility entries, claims, and cells. `matched_B_frames_field_change`
transports the correlation. Existing rich owner coverage proves at most one
live carrier class and no live holder after release.

## Concrete finite evidence

`NewLang/Adjunct/Counterexample/BComposition.lean` starts with the accepted
`wired6` five original independent roots and three sibling fields. Six NEW
checked Changes perform:

1. A.next=C; C.prev=A; B.prev=None; B.next=None.
2. dst.child=B; B.prev=B.

Every transition has actual `Replace` applicability and derived WellFormedness.
`four_detach_relations`, `two_adoption_relations`, and
`all_link_updates_preserve_five_originals` prove the links and unchanged five
O/R/D/Allocation origin descriptors, owners, claims, and cells. Adoption changes
Copy links, not custody (`graph_adoption_does_not_move_B_responsibility`).

Actual primitive cleanup releases src, then A, then C while original B and dst
remain live. `donor_cleanup_keeps_original_B_dst_live` proves that frame;
`skipped_B_release_leaves_nonCopy_residue` records three frees and B's remaining
responsibility. `independent_B_primitive_cleanup_still_available` proves primitive
B cleanup is possible. It is NOT a recipient-authorized delayed release.
The existing real 0..5 allocation-failure cleanup traces and exact release
counts are retained by `pre_transfer_failure_worlds_remain_guarded`.
`refusal_is_a_rich_heap_frame` is a structural old rich refusal frame, not a
new five-root actual refusal call certificate.

## Minimal missing interfaces / countermodels

1. **World ledger versus donor availability.** FiveRoot owners is world-wide
   responsibility, not the current donor's local bindings. Removing B's entries
   while B is live makes a concrete state malformed
   (`naive_donor_cut_is_not_an_adapter`). Leaving them unchanged cannot prove the
   donor has lost availability: the existing `CanEnd` has no custodian input
   (`field_changes_do_not_revoke_old_end_permission`). A sound adapter must
   correlate the world ledger with one principal-local current binding carrier
   and prove actual call rebinding consumes donor availability. Neither Copy
   links nor a second invented owner table supplies that proof.
2. **Caller-owned sum versus independent receiver.** The accepted F #39
   recipient requires a caller-owned Option destination and preserves that same
   container after returning unit. This follows from the actual call relation
   (`accepted_recipient_preserves_caller_owned_destination`), with a real old
   two-root witness (`old_recipient_has_caller_owned_sink`). A receiver-owned
   destination is rejected by its current applicability. Relabeling the
   `custody` holder as an independent principal would overclaim the evidence.
   The missing interface is a correlated retained carrier/application proof
   for an explicitly distinct receiving custodian, using accepted mechanisms.
3. **Delayed receiver after donor head release.** Project the ACTUAL donor-done
   A/B cells into the old terminal head=A/tail=B view. Both ContextValid and
   WellFormed hold, exact original B identity/current carriers survive, and all
   entry obligations other than head-live compute successfully
   (`projected_entry_if_head_live`). Nonetheless every old `KnownCall.Call` is
   rejected because A is released (`delayed_B_call_has_concrete_head_blocker`).
   This is an interface-precondition countermodel, not a language impossibility.
   A separately proved receiver-view/frame adapter (possibly using live dst)
   is required; silently rebasing the existing approved rich head breaks its
   invariant (`approved_head_cannot_be_rebased`). We do not remove head-live or
   assume a future receiver's correctness.

These adapters are not introduced here because their actual call/principal
correlation is precisely the missing evidence. The accepted field frame alone
cannot establish the complete requested pipeline.

## Negative controls and policy separation

Machine-checked controls include Copy dst.child failing to repair a missing B
Allocation/Domain carrier; simultaneous donor+recipient support impossible;
B end under a scoped loan rejected; crossed C Domain rejected; skipped B
release leaving nonCopy residue; old A.next occurrence dead after a fresh
Change; receiver-owned sink not applicable; and terminal call after old head
release rejected. `wrong_graph_policy_is_still_memory_wellFormed` shows a skipped
A.next rewire can violate intended graph policy while remaining memory
WellFormed. It is not a language memory-unsafety result.

## Findings and limits

- FORMAL-ENCODING: principal-local availability and the five-root global ledger
  need a correlated adapter; origin Allocation labels are not current bindings.
- FORMAL-ENCODING: the old caller-owned recipient is not a distinct execution
  principal; the approved two-root head is not freely rebasable.
- FORMAL-LEMMA: generic field frame and conditional actual-call transport are
  proved; missing concrete matched application must not be inferred from them.
- FORMAL-SCOPE: complete distinct-principal accept/refuse, donor loss of B
  availability, and recipient B/dst delayed terminal release are UNPROVED here.
- No canonical FORMAL-HOLE / FORMAL-AMBIGUITY is established. No normative
  strengthening, global owner API, implicit Drop, source grammar, production
  checker/backend refinement, heap-native C, or cJSON success is claimed.

## Verification and review

Baseline build and all 1512 original audits passed. Candidate adds 56 audited
public declarations (1568 total), preserving the whitelist of standard Lean
logic dependencies. `lake build` and `bash scripts/check-proofs.sh` pass with
no project-owned proof placeholders or custom semantic axioms. Lean 4.34.1 /
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pins are unchanged.
Exact committed candidate head, OPEN/unmerged PR and fixed-head GitHub Actions
results are recorded in the Issue #43 handoff; Git is the change-history source.

F FIVE-ROOT B-CUSTODY COMPOSITION: HOLD — MINIMAL SEMANTIC ADAPTER OR COUNTERMODEL
