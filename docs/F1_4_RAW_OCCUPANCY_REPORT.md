# F1.4 — Raw occupancy / Storage / slot responsibility conservation

[日本語（primary）](F1_4_RAW_OCCUPANCY_REPORT.ja.md)

Status: **F1.4 IMPLEMENTATION COMPLETE / F1.4 READY FOR REVIEW**. This is a proof report, not a normative language document or merge decision. Change history is Git; no independent version history is maintained.

## Process, authority and baseline

- Task: [FormalProof Issue #13](https://github.com/wakairo/NewLang_FormalProof/issues/13). Substantive Issue comments identify **Track: F**.
- Process read first: [Compiler development process](https://github.com/wakairo/NewLang_Compiler/blob/d4eff722fc7ee1a609875b51dcecbbf953dfe737/docs/NewLang_Project_Development_Process.md).
- Compiler main checked: `d4eff722fc7ee1a609875b51dcecbbf953dfe737`; `docs/reference/CURRENT_SPEC.md` selects canonical **Draft 17.8**. Inspected §3.3–3.5, §14.1–3 and §23.1. P4 reports are historical evidence, not authority; their old empty/endpoint ambiguity is not inherited.
- FormalProof main/base checked: `1446011d7a9fa1b16fcb0cbbe88b660a57d28f2d`. F1.3 is reviewed/merged/CLOSED. Before changes: `lake build` PASS, `scripts/check-proofs.sh` PASS **639**.
- Branch: `f1.4-raw-occupancy-storage-slot`. Main is untouched. PR remains open/unmerged. No F1.5/P5/M9/Sync/Red Team task is started.

## Encoding and claim boundary

`Range` is a half-open region-relative ordinal interval `(base,length)`. `Extent` adds the existing F1.3 nominal BackingRegionId. Geometry injects relative coordinates into the existing abstract byte instances and agrees with World.bytes; relative ordinals are not numeric machine addresses and do not derive authority. RegionsDisjoint remains controlling for independent live regions.

`Layout` is a static type-key-to-size proof context with positive size for storable T, as required by Draft 17.8 §23.1. Into_slot requires **e.length = sizeof(T)** and caller alignment. Representation validity/type/ending applicability remains in the reviewed caller propositions. No concrete ABI/layout arithmetic or frontend type derivation is claimed.

The proof-only finite Ledger has a fixed explicit region scope, active ghost ClaimId handles and inert inactive table records. The claim variants are:

- `storage e`: value-owned raw responsibility, affine/non-Copy/non-Discardable;
- `slot t e`: value-owned definitely-empty typed responsibility, no semantic T value;
- `root t location e`: the accounting view of that same state-owned live placement, **not** a second owner of its bytes.

Ghost handle allocation means not currently active; reusing inactive handles is allowed. It is deliberately not historical object identity or a new identity supply. The reviewed incarnation/value/occurrence histories and stale rules remain untouched. No runtime history set, ledger, shadow bitmap or source-visible owner is required. **Formal representation choices are non-normative.**

AccountingShape has geometry compatibility, independent-region separation, live scope, claim-in-scope, positive length, exact fit, static typed size, exact live-root correspondence and exact placement correspondence. Accounting adds global NoOverlap and **complete exact coverage of the explicitly scoped regions**. Live regions outside scope are allowed; this is not a full allocator ownership algebra. No-overlap concerns independent occupancy responsibilities, not fixed ancestors/descendants. Every modeled byte has exactly one active responsible handle, and every raw/empty/live claim requires live backing.

## Operations and substantive results

Split atomically consumes a raw carrier, requires `0 < k < n`, and creates two same-region nonempty fragments with disjoint exact union. Merge atomically consumes two distinct same-region nonempty adjacent raw carriers; either relative order is legal and the exact union is contiguous. Both conserve **the entire ledger footprint** and preserve NoOverlap against every framed claim. An immediate split→merge witness accepts both argument orders.

Into_slot consumes precisely one exact-size raw carrier into its same-extent empty typed claim; no tail split or byte loss is implicit. Erase_slot consumes the empty carrier into same-extent Storage, without read/write applicability; it is universally safe/total for well-formed valid slot input. Those conversions derive Accounting post validity from pre plus raw operation.

Lifecycle wrappers reuse actual reviewed F1.3 RawInitialize/RawTake/RawDestroy. Initialize consumes the supplied slot and installs a root at its exact region/range. Take returns the same empty responsibility and a surviving semantic T with no source-placement ownership. Destroy also returns the same empty responsibility; static Discardable/ending conditions remain in reviewed F0/F1.3 premises. Initialize requires write; take requires ptr/backing read; destroy has no take-read guard. Ending the root leaves backing and accounting scope live. Same-range fresh restart is legal and old ptr remains stale.

Legal split/merge/lifecycle steps retain the reviewed **raw candidate + checked pre/post invariants** discipline. No theorem assumes every arbitrary raw lifecycle candidate is semantically well formed. Conservation and global disjointness are proved separately; complete legal endpoints establish non-vacuity. This is not a general transition framework or proof of omitted caller/static obligations.

A concrete four-byte region is split into two halves. The left half goes through into_slot → initialize → take → same-range fresh initialize → destroy → erase_slot, while the right raw half remains outstanding. Merge returns one exact full Storage; source carriers are consumed and root identity history is retained. Separate WO initialize/destroy witnesses establish that destroy did not inherit read. All fixture constants are proof witnesses, not normative runtime layouts.

## Erasure and precision

Flat WellFormed explicitly inherits the nine reviewed semantic fields. PhysicalWellFormed is **derived** from Accounting, not a hidden erased-WF assumption. Flat erasure drops ledger/relative-range/static-layout precision and retains the exact reviewed F1.3 flat state, then F0 obligations. A separate conditional product explicitly inherits the reviewed F1.2 Invariant and its same single DependenciesValid; it derives backing validity and then uses unchanged F1.3→F1.2→F1.1→F0 erasures. This does not implement sum lifetime start/end, arbitrary typed-layout embedding or exact Step simulation.

Representation-only mutation is modeled solely as an **authority frame** with an opaque contents marker. A concrete contents change keeps the entire semantic/physical/claim authority state unchanged. No byte-validity semantics or actual storage_read/write/copy operations are implemented; no proof of frontend pointer minting or arbitrary unsafe raw operations is implied.

## Required isolated controls

Controls live under `NewLang.F1.Occupancy.Counterexample`, separate from production. Fully valid wrong-range endpoints redistribute the complementary raw half too; the exact candidate/frame relation rejects them. Overlap cannot be a well-formed merge source by definition, so that control explicitly retains shape/coverage while showing the independent overlap failure.

| Issue control | Rule | Audited declaration(s) | Isolation / result |
| --- | --- | --- | --- |
| 1 | Endpoint split / empty Storage | `endpoint_split_controls` | Valid raw source; both endpoint results have length 0; RawSplit rejects. |
| 2 | Split gap / lost byte | `gap_split_isolates_lost_responsibility` | All AccountingShape and NoOverlap hold; byte 1 loses coverage. |
| 3 | Split overlap / duplicate byte | `overlapping_split_isolates_duplication` | All shape and exact coverage hold; byte 2 breaks only NoOverlap. |
| 4 | Different-region merge | `different_region_merge_isolates_identity` | Complete valid two-region source with nonempty relatively adjacent inputs; nominal identity guard rejects. |
| 5 | Merge gap / overlap | `merge_gap_and_overlap_controls` | Gap source is fully accounted, with a third raw carrier filling the gap; gap/overlap are nonadjacent. Overlap intentionally breaks pre disjointness too. |
| 6 | Larger into_slot / dropped tail | `larger_into_slot_tail_control`; `unchecked_into_slot_loses_tail` | Valid source and exact-size endpoints; larger input rejects. Private tail-drop candidate retains shape/NoOverlap and loses only coverage, at byte 2. |
| 7 | Storage + slot duplicate | `storage_and_slot_overlap_isolated` | Semantic validity, all shape and coverage remain; only NoOverlap fails. |
| 8 | Slot + live-root duplicate | `slot_and_live_root_overlap_isolated` | Semantic validity, all shape and coverage remain; only NoOverlap fails. |
| 9 | Initialize at wrong range | `initialize_wrong_range_control_has_valid_endpoints` | Both states are fully well formed and the semantic post matches; wrong placement violates raw exact-destination relation. |
| 10 | Take returns wrong slot range | `take_wrong_slot_control_has_valid_endpoints` | Both states are fully well formed, including exact reviewed flat take post; ledger frame/exact-slot relation rejects. |
| 11 | Destroy loses responsibility | `destroy_lost_responsibility_control` | Semantic validity, shape and NoOverlap remain; left bytes lose coverage and required returned slot is absent. |
| 12 | Erase_slot mints wrong/larger Storage | `erase_slot_wrong_range_control_has_valid_endpoints`; `erase_slot_larger_or_different_region_controls` | Wrong-range case has fully valid endpoints; independent larger/different nominal region controls reject exact conversion. |
| 13 | Reconstruct full Storage with outstanding subclaim | `outstanding_slot_blocks_full_storage`; `outstanding_root_blocks_full_storage` | All shape/coverage remain; independent full Storage duplicates slot/root responsibility. Universal full_region_storage_excludes_outstanding_subclaim also covers raw subclaims. |

## Formal findings and exclusions

- **FORMAL-ENCODING:** Relative intervals/geometry, ghost carrier handles, complete explicit region scope and root placement accounting are proof representations. They do not impose runtime metadata or another physical identity model.
- **FORMAL-LEMMA:** Exact footprint conservation plus global disjointness yields no loss/duplication; live-backed unique responsibility and total erase conversion are separately checked. Access/stale lifetime evidence is inherited from reviewed operations.
- **FORMAL-EXTRACTION — resolved report interpretation:** The prior F1.3 report said unconstrained empty extents allow zero-sized roots. Canonical Draft 17.8 §23.1 requires `sizeof(T) >= 1` for every storable type. Minimal witness to the distinction: an untyped F1.3 empty Placement has no typed exact-size proof and therefore establishes no storable zero-sized object. The report now states that limited encoding boundary. No canonical rule, F1.3 code, public theorem or whitelist changed; positive exact-size accounting is added conservatively here.
- **FORMAL-HOLE / FORMAL-AMBIGUITY:** **none** found in inspected canonical rules. No unresolved canonical extraction issue needs Coordination adjudication. Endpoint/nonempty/exact-size rules are explicit.
- **FORMAL-SCOPE:** No Allocation/deallocator policy, allocator failure, relocation, numeric pointer authority, general dynamic-container ownership, ancestor/child non-overlap, FFI/MMIO/volatile, frontend/P5/M9, per-byte Defined state, mandatory shadow bitmap or full raw-byte operations. No Semantic Sync Review is run.

## Verification, CI and review handoff

Lean/Lake remains `leanprover/lean4:v4.34.1` (release commit `5045d0056413266e57c625dcd7c365b10e377c52`); elan remains 4.2.4; mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. Toolchain/manifest/bootstrap/workflow are unchanged.

Local `lake build` and `bash scripts/check-proofs.sh` PASS. All 639 existing audited declarations retain their original order. All **118** new public theorems are appended: **76 production/helper + 42 validation/helper**, total **757**. Project-owned sources contain no prohibited placeholders/custom semantic assumptions; only `propext`, `Classical.choice`, `Quot.sound` are allowed, unchanged. Private support proofs are kernel-checked through the audited declarations; no new automation/allocator framework is introduced.

The unchanged `Lean proofs` workflow bootstraps the pinned environment on push/pull_request. The exact final-head **pull_request** run/job URL, success status, PR number and head SHA are recorded in the [Issue #13 Track: F READY FOR REVIEW handoff](https://github.com/wakairo/NewLang_FormalProof/issues/13). That GitHub evidence is the review-head CI record; this report does not maintain a duplicate self-referential commit/version log. READY is published only after that exact-head check succeeds. PR remains open/unmerged and main stays unchanged.

## Exact additional audited theorem inventory

The following list is the complete set of 118 appended public declarations; generated structure projections and private support lemmas are not separately counted. Every declaration below is checked by the retained standard-logic audit.

### [NewLang/F1/Occupancy/Claims.lean](../NewLang/F1/Occupancy/Claims.lean) — 21

Namespace: `NewLang.F1.Occupancy`.

- `consumeOne_active_iff`
- `consumeOne_consumes_source`
- `consumeOne_produces_result`
- `consumeOne_conserves_footprint`
- `split_consumes_source_and_produces_two`
- `split_preserves_identity_nonempty_partition`
- `split_rejects_left_endpoint`
- `split_rejects_right_endpoint`
- `split_conserves_all_byte_responsibility`
- `split_preserves_scope`
- `merge_consumes_both_inputs`
- `merge_preserves_identity_and_exact_union`
- `merge_rejects_different_regions`
- `merge_rejects_nonadjacent`
- `merge_conserves_all_byte_responsibility`
- `into_slot_consumes_raw_exact_range`
- `into_slot_rejects_larger_range`
- `into_slot_conserves_all_byte_responsibility`
- `erase_slot_consumes_empty_exact_range`
- `erase_slot_conserves_all_byte_responsibility`
- `erase_slot_has_no_access_precondition`

### [NewLang/F1/Occupancy/Conversion.lean](../NewLang/F1/Occupancy/Conversion.lean) — 6

Namespace: `NewLang.F1.Occupancy`.

- `empty_conversion_preserves_accounting`
- `into_slot_step_of_raw`
- `erase_slot_step_of_raw`
- `erase_slot_is_total`
- `empty_claim_conversion_preserves_flat`
- `empty_claim_conversion_preserves_sum`

### [NewLang/F1/Occupancy/Counterexample/Claims.lean](../NewLang/F1/Occupancy/Counterexample/Claims.lean) — 9

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `endpoint_split_controls`
- `gap_split_isolates_lost_responsibility`
- `overlapping_split_isolates_duplication`
- `merge_gap_and_overlap_controls`
- `different_region_merge_isolates_identity`
- `different_region_merge_control`
- `larger_into_slot_tail_control`
- `unchecked_into_slot_loses_tail`
- `split_merge_roundtrip_is_legal`

### [NewLang/F1/Occupancy/Counterexample/Cycle.lean](../NewLang/F1/Occupancy/Counterexample/Cycle.lean) — 19

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `single_raw_accounting`
- `raw_state_wellFormed`
- `split_is_legal`
- `slot_state_wellFormed`
- `into_slot_is_legal`
- `first_wellFormed`
- `taken_wellFormed`
- `restart_wellFormed`
- `ended_wellFormed`
- `initialize_is_legal`
- `take_is_legal`
- `same_range_restart_is_legal_and_old_ptr_stays_stale`
- `destroy_is_legal`
- `erase_slot_is_legal`
- `merged_wellFormed`
- `merge_after_lifecycle_is_legal`
- `writeonly_destroy_is_legal`
- `writeonly_take_rejected_but_destroy_allowed`
- `complete_responsibility_cycle`

### [NewLang/F1/Occupancy/Counterexample/Fixtures.lean](../NewLang/F1/Occupancy/Counterexample/Fixtures.lean) — 4

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `live_iff`
- `semantic_wf`
- `pair_shape`
- `pair_accounting`

### [NewLang/F1/Occupancy/Counterexample/Lifetime.lean](../NewLang/F1/Occupancy/Counterexample/Lifetime.lean) — 6

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `initialize_wrong_range_control_has_valid_endpoints`
- `take_wrong_slot_control_has_valid_endpoints`
- `erase_slot_wrong_range_control_has_valid_endpoints`
- `destroy_lost_responsibility_control`
- `erase_slot_larger_or_different_region_controls`
- `representation_change_is_possible_without_new_authority`

### [NewLang/F1/Occupancy/Counterexample/Overlap.lean](../NewLang/F1/Occupancy/Counterexample/Overlap.lean) — 4

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `storage_and_slot_overlap_isolated`
- `slot_and_live_root_overlap_isolated`
- `outstanding_slot_blocks_full_storage`
- `outstanding_root_blocks_full_storage`

### [NewLang/F1/Occupancy/Lifetime.lean](../NewLang/F1/Occupancy/Lifetime.lean) — 19

Namespace: `NewLang.F1.Occupancy`.

- `initialize_consumes_slot_and_preserves_exact_responsibility`
- `initialize_conserves_byte_responsibility`
- `initialize_preserves_backing_lifetime_and_scope`
- `initialize_requires_reviewed_write_access`
- `initialize_rejects_readonly_backing`
- `initialize_step_erases_to_backing`
- `take_consumes_root_and_returns_same_slot`
- `destroy_consumes_root_and_returns_same_slot`
- `take_conserves_byte_responsibility`
- `destroy_conserves_byte_responsibility`
- `take_does_not_end_backing`
- `destroy_does_not_end_backing`
- `take_transfers_value_without_placement`
- `take_requires_reviewed_read_access`
- `take_rejects_writeonly_ptr`
- `take_step_erases_to_backing`
- `destroy_step_erases_to_backing`
- `take_then_same_range_restart_rejects_stale_ptr`
- `representation_mutation_cannot_mint_authority`

### [NewLang/F1/Occupancy/Model.lean](../NewLang/F1/Occupancy/Model.lean) — 13

Namespace: `NewLang.F1.Occupancy`.

- `accounting_derives_physical_wellFormed`
- `wellFormed_erases_to_backing`
- `wellFormed_erases_to_f0`
- `sum_wellFormed_erases_to_backing`
- `sum_wellFormed_erases_to_conditional`
- `sum_wellFormed_erases_to_current`
- `sum_wellFormed_erases_to_f0`
- `surviving_claim_requires_live_backing`
- `every_scoped_byte_has_unique_responsibility`
- `nonempty_claim_cannot_be_covered_twice`
- `full_region_storage_excludes_outstanding_subclaim`
- `storage_is_affine_nonDiscardable`
- `slot_is_empty_authority_not_live_value`

### [NewLang/F1/Occupancy/Partition.lean](../NewLang/F1/Occupancy/Partition.lean) — 2

Namespace: `NewLang.F1.Occupancy`.

- `split_preserves_no_overlap`
- `merge_preserves_no_overlap`

### [NewLang/F1/Occupancy/Range.lean](../NewLang/F1/Occupancy/Range.lean) — 15

Namespace: `NewLang.F1.Occupancy`.

- `range_membership`
- `nonempty_range_has_position`
- `split_ranges_are_nonempty`
- `split_ranges_exact_union`
- `split_ranges_disjoint`
- `split_extents_preserve_region`
- `split_extents_exact_union`
- `split_extents_disjoint`
- `adjacent_ranges_disjoint`
- `adjacent_ranges_exact_union`
- `adjacent_extents_exact_union`
- `adjacent_extents_disjoint`
- `split_merge_range_roundtrip`
- `extent_footprint_nonempty`
- `fitting_extent_is_inside_backing`
