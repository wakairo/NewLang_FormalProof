# F1.3 — BackingRegion / placement / access boundary

Status: **F1.3 IMPLEMENTATION COMPLETE / F1.3 READY FOR REVIEW**. Dedicated branch `f1.3-backing-placement-access`; PR remains open and unmerged. Git is the change history.

## Authority and baseline

- Handoff: [FormalProof Issue #10](https://github.com/wakairo/NewLang_FormalProof/issues/10).
- Canonical repository: `wakairo/NewLang_Compiler`, exact main `3d5f7249fcce5a01fe9bb1616dbe7d469f192d12`.
- [CURRENT_SPEC selector](https://github.com/wakairo/NewLang_Compiler/blob/3d5f7249fcce5a01fe9bb1616dbe7d469f192d12/docs/reference/CURRENT_SPEC.md) selects [Draft 17.8](https://github.com/wakairo/NewLang_Compiler/blob/3d5f7249fcce5a01fe9bb1616dbe7d469f192d12/docs/reference/NewLang_v0_spec_Draft17_8.md).
- FormalProof base main: `70e7c63beacf9234a0b924b1e6cbf30ab9ef4b94`, with F0–F1.2 merged. Both current mains matched the issue's exact baselines before implementation.
- End-of-task authority recheck: Compiler main advanced to `d4eff722fc7ee1a609875b51dcecbbf953dfe737` with development-process documentation changes only; CURRENT_SPEC and Draft 17.8 are unchanged. The proof remains pinned to Issue #10's exact canonical snapshot. FormalProof main remains the base SHA above.
- Baseline `lake build`: PASS, 705 jobs. Baseline proof audit: PASS, all 567 declarations.
- Inspected authority: §3.1 (nominal regions and abstract backing-byte non-aliasing), §3.5 (incarnation and state-owned placement), §14.1–3 (ordinary start/take/destroy access), and existing §13.5a/§17.4 current-value/dependency boundaries. Draft 17.8 explicitly requires take-read while distinguishing atomic destroy.

The local Draft 17.4 remains an unchanged historical snapshot. The bridge is non-normative. No canonical specification is edited. **Formal representation choices are non-normative.**

## Model and claim boundary

`F1.Backing` adds nominal `BackingRegionId` and `AbstractByteId`, independent of place, location, incarnation, package and value-fact IDs. The latter denotes an opaque abstract byte instance, never an address or offset. `World` carries live-region support, abstract backing-byte extents and ordinary read/write properties. Independent live regions cannot alias those instances.

`PhysicalState.placement : RootLocationId → Option Placement` is state-owned. `Placement` names one region and a finite occupied abstract-byte extent. Every live root has exactly one relation, every relation backs a live root in a live region, and its extent fits that region. Independent explicit root extents are disjoint. This does not impose disjointness on fixed ancestors/children. Empty extents are not prohibited, allowing zero-sized roots. Contiguity, alignment, typed exact extent and valid representation remain caller responsibilities; finite sets do not implement layout or Storage claims.

`AccessLe` compares read and write independently. `EvidenceValid` requires a live region and componentwise access no greater than its backing. An `AccessPtr` combines reviewed location/incarnation provenance with separate access evidence. `CurrentAccessPtr` additionally checks the exact current incarnation and region of the live placement. Pure construction alone grants no safe authority.

There are two deliberately bounded adapters:

1. `SumState` refines the reviewed root-level F1.2 sum slice. `SumWellFormed` lists the inherited semantic shape/frame obligations, the same single surviving dependency invariant, and physical obligations. Whole/payload updates and swap lift the existing relational candidates, retain physical state, and require backing write in addition to caller write/type propositions. Generic lift theorems derive physical post validity from unchanged live-root support, rather than assuming it separately. Whole/payload/swap legal steps erase to their actual reviewed F1.2 steps.
2. `FlatState` is a minimum lifecycle/access slice over reviewed F0 occupancy. Its invariant retains all nine semantic obligations plus physical validity. It reuses existing raw initialize/take/destroy instead of implementing sum lifetime start/end, Storage/slot ownership or a generic transition framework. Legal steps require checked semantic and physical endpoints. Their erasure is explicitly an assembly/projection of inherited obligations, not a claim that geometry alone establishes semantic safety.

Sum erasure forgets physical/access precision, retains the exact F1.2 semantic state, then uses the unchanged F1.2→F1.1 CurrentWellFormed and F1.1→F0 proofs. No hidden `WellFormed(erased)` premise is added. The flat product also exposes the inherited obligations directly. No full sum-to-flat lifetime simulation, arbitrary fixed-layout backing derivation or physical safety completeness is claimed.

## Operation results

| Operation | Placement/access result |
| --- | --- |
| Whole replace/store | Target and all other placements/world remain; reviewed package/survivor/occurrence rules remain |
| Payload replace/store | Enclosing root placement/world remain; occurrence behavior comes from the reviewed F1.2 relation |
| Same-place swap | Exact state identity, with no placement or history allocation |
| Distinct swap | Semantic packages exchange; package/dependency data and destination placements do not move |
| Ordinary initialize | Explicit destination relation; valid supplied evidence must write; ptr evidence is exactly supplied evidence and cannot amplify backing |
| Ordinary take | Exact current token/region, readable ptr evidence and readable backing; source relation ends, value survives without source placement |
| Ordinary destroy | Exact current token/region, Discardable value and caller end contract; source relation ends without a take-read condition |
| Same-placement restart | Fresh reviewed incarnation history; the old token stays stale even with identical region/extent |

Initialization's caller propositions include typed empty-destination responsibility, geometric/type applicability, representation and alignment. Root ending retains the same World; region finalization/deallocation is not inferred or implemented. Destroy's caller contract can include platform-specific end requirements; absence of a generic read guard does not waive that contract.

No placement field was added to any semantic value/package. A concrete take/reinitialize transfer keeps identical package data but uses a different root location and explicitly supplied destination region. Backing authority comes from destination evidence, never the returned package. Numeric addresses are omitted from the production model; the isolated equal-label control establishes only that an arbitrary hypothetical address label cannot identify nominal regions or grant authority.

## Witnesses and isolated controls

| Control | Evidence and isolated failure |
| --- | --- |
| Backed sum witnesses | Concrete reviewed independent replace, old-only-dependency store, distinct swap and exact same swap lift to one-byte-per-root backing; also every reviewed sum-WF state has such a physical witness |
| Source placement attached to transferred value | Legal transfer into region 1 preserves package data. The region-0 wrong destination remains fully WF and semantically identical, but fails the explicit destination relation |
| Placement exchanged with packages | Concrete reviewed legal distinct semantic swap and fully valid geometry at both endpoints; only the physical frame fails the backing RawSwap |
| Dead backing | All original semantic obligations, region non-aliasing, placement/root correspondence, extent fit and root disjointness remain; only live-region membership fails |
| Read-only initialize | WF endpoints, F0 raw start, valid evidence, fit/separation and exact physical candidate all hold; only ordinary write applicability fails |
| Amplified ptr evidence | Write-only initialized current ptr is valid; upgrading its evidence to read+write fails EvidenceValid |
| Write-only take | WF endpoints, existing F0 take, current ptr/evidence and physical end candidate all hold; only read applicability fails |
| Broken destroy-read guard | Production Discardable write-only destroy is legal; an isolated extra take-read guard rejects that same case. The extra guard is not a Draft 17.8 language requirement |
| Stale-token revival | Legal RW take followed by legal fresh initialize at identical placement, with recorded history retained; CurrentAccessPtr rejects the old token |

Negative controls are private definitions inside `Counterexample/Boundary.lean`, with public machine-checked outcome theorems. Existing F1.2 dependency controls remain unchanged. Source/destination placement errors can be geometrically WF, so they are checked as operation-frame/applicability errors rather than distorting the state invariant.

## Formal findings and exclusions

- **FORMAL-ENCODING:** Finite abstract extents and two root-level adapters conservatively expose backing/access facts without encoding byte content, numeric addresses, runtime tags or authority algebra.
- **FORMAL-LEMMA:** State-owned placement, live backing, access non-amplification, take/destroy distinction and stale-token separation are proved; negative controls isolate missing guards/frame obligations.
- **FORMAL-SCOPE:** Exact typed geometry and source capability derivation remain caller propositions. Storage/slot/raw occupancy conservation, allocation/deallocation, raw Defined/Unspecified, relocation, pointer arithmetic, FFI/MMIO/volatile, lexical future-use checking, frontend, full sum lifecycle and arbitrary fixed-subobject placement derivation remain out of scope. No F1.4/F1.5/P5/M9 semantics are added.
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION:** None in the inspected canonical rules. No concern requires Coordinator adjudication. Existing resolved bridge-number history is preserved. Present-tense README/notes authority and milestone status are corrected without a separate version-history log.

## Verification

Lean/Lake `leanprover/lean4:v4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, elan/bootstrap checksums, manifest and CI workflow are unchanged. All 567 prior audit declarations remain in original order; 72 additions yield **639**. Only the existing `propext`, `Classical.choice`, `Quot.sound` whitelist is allowed. Project-owned Lean sources have no proof placeholders or custom semantic assumptions.

Final local verification: `lake clean newlang-formal` followed by `lake build`: **PASS (709 jobs)**; `bash scripts/check-proofs.sh`: **PASS (639 reports)**. All prior sources were rebuilt, all 567 prior audit entries were verified retained in order, and project-owned placeholder scan passed. The existing **Lean proofs** workflow is reused without changes.

[PR #11](https://github.com/wakairo/NewLang_FormalProof/pull/11) targets main and remains open/unmerged. The [implementation PR-event run](https://github.com/wakairo/NewLang_FormalProof/actions/runs/37280671840) succeeded for head `c77e461645f30e17be4c2e00b64b9a5e0fb65b30` (job `proofs`). The final-head run permalink, exact SHA, event and job verdict are maintained in the PR body and [current PR checks](https://github.com/wakairo/NewLang_FormalProof/pull/11/checks), so the branch does not embed its own self-referential commit hash. READY FOR REVIEW handoff requires that final-head PR event to succeed.

## Exact new audited inventory (72)

Every public theorem below is imported by `NewLang.lean` and included in `scripts/check-proofs.sh`; all private fixture helpers are transitively kernel-checked.

### `NewLang/F1/Backing/Counterexample/Boundary.lean` (25)

Namespace: `NewLang.F1.Backing.Counterexample.Boundary`.

- `every_conditional_wellFormed_state_has_backing`
- `independent_whole_replace_has_backing`
- `old_only_dependency_store_has_backing`
- `independent_distinct_swap_has_backing`
- `same_sum_swap_with_backing_is_exact_noop`
- `distinct_placement_is_not_exchanged`
- `broken_package_placement_exchange_breaks_frame`
- `broken_package_placement_exchange_is_geometrically_valid`
- `readwrite_initialize_is_legal`
- `writeonly_initialize_is_legal`
- `readwrite_take_is_legal`
- `writeonly_destroy_is_legal`
- `writeonly_take_is_rejected`
- `readonly_initialize_is_rejected`
- `broken_destroy_read_guard_rejects_valid_language_case`
- `same_placement_restart_is_legal_but_old_ptr_is_stale`
- `readonly_control_isolates_write_applicability`
- `writeonly_take_control_isolates_read_applicability`
- `stronger_ptr_evidence_is_rejected`
- `dead_backing_control_isolates_region_liveness`
- `equal_hypothetical_addresses_do_not_identify_regions`
- `value_transfer_installs_at_destination_not_source`
- `broken_value_owned_source_placement_is_rejected`
- `swap_rejects_package_owned_placement_exchange`
- `broken_swap_control_keeps_semantics_and_geometry_valid`

### `NewLang/F1/Backing/Current.lean` (14)

Namespace: `NewLang.F1.Backing`.

- `whole_preserves_placement`
- `whole_replace_preserves_target_placement`
- `whole_store_preserves_target_placement`
- `whole_lift_is_legal`
- `payload_preserves_placement`
- `payload_backing_wellFormed`
- `swap_same_is_identity`
- `swap_preserves_placement_and_backing`
- `swap_lift_is_legal`
- `swap_distinct_exchanges_values_not_placement`
- `whole_step_erases`
- `swap_step_erases`
- `payload_lift_is_legal`
- `payload_step_erases`

### `NewLang/F1/Backing/Lifetime.lean` (23)

Namespace: `NewLang.F1.Backing`.

- `initialize_requires_destination_write`
- `initialize_rejects_readonly_region`
- `initialize_rejects_readonly_evidence`
- `initialize_uses_destination_placement`
- `initialize_preserves_other_placements`
- `initialize_produces_current_ptr`
- `initialize_ptr_access_nonamplification`
- `initialize_value_transfer_does_not_transfer_placement`
- `initialize_reused_placement_does_not_revive_old_ptr`
- `take_requires_source_read`
- `take_rejects_writeonly_ptr`
- `take_rejects_writeonly_region`
- `take_ends_placement_not_backing`
- `destroy_ends_placement_not_backing`
- `take_live_region_remains_live`
- `destroy_live_region_remains_live`
- `take_transfers_value_without_source_placement`
- `destroy_requires_discardable`
- `take_then_restart_rejects_old_ptr`
- `destroy_then_restart_rejects_old_ptr`
- `initialize_step_erases`
- `take_step_erases`
- `destroy_step_erases`

### `NewLang/F1/Backing/Model.lean` (10)

Namespace: `NewLang.F1.Backing`.

- `accessLe_refl`
- `accessLe_trans`
- `evidence_cannot_amplify_read`
- `evidence_cannot_amplify_write`
- `sum_wellFormed_erases_to_conditional`
- `sum_wellFormed_erases_to_current`
- `sum_wellFormed_erases_to_f0`
- `flat_wellFormed_erases_to_f0`
- `live_root_requires_live_region`
- `dead_region_cannot_back_live_root`
