# F1.2 — Conditional Occurrence / Sum Semantics

Status: **F1.2 IMPLEMENTATION COMPLETE / F1.2 READY FOR REVIEW**. Review and merge remain human decisions. F1.3 is not implemented.

## Canonical authority and baseline

Both repositories' current main branches were checked before implementation:

- FormalProof base: `f07d51822bd641ddf77a09be1a595ac40e3a34de` (F0.0–F0.6 / F1.0 / F1.1 CLOSED/MERGED).
- Compiler main: `aacb53b3cc599276125e7420d7cb4a5dbae19b5c`.
- [Canonical selector](https://github.com/wakairo/NewLang_Compiler/blob/aacb53b3cc599276125e7420d7cb4a5dbae19b5c/docs/reference/CURRENT_SPEC.md) selects [Draft 17.6](https://github.com/wakairo/NewLang_Compiler/blob/aacb53b3cc599276125e7420d7cb4a5dbae19b5c/docs/reference/NewLang_v0_spec_Draft17_6.md).

The inspected rules are Draft 17.6 §13.5a (place-owned versus value-owned state, exact facts, surviving dependencies), §17.4 (atomic updates and same/distinct sum swap), and §26.4 / §26.6–8 / §26.16–23 / §26.27–28. `docs/NewLang_v0_spec_Draft17_4.md` remains an unchanged historical local snapshot. The F0 bridge is non-normative and is not current language authority.

Baseline `lake build` passed (701 jobs); `scripts/check-proofs.sh` passed all **467** existing declarations. Existing F0/F1.0/F1.1 Lean definitions and public theorem statements are unchanged. Git is the change history; this report does not maintain a separate version history.

## State and value extension

The new namespace is `NewLang.F1.Conditional`. Its state is a finite **root-level nominal closed-sum slice**, with opaque payload values. `SumTypeId`, `VariantId`, and `OccurrenceId` are nominal types. A type table fixes the closed set of possible variants, payload presence and each possible payload type's static Discardable capability. Whole-sum Discardable is the conjunction over **all possible payload types**, with payloadless variants contributing true.

A `SumRoot` owns place, incarnation, current value fact, installed carrier, governing domain and nominal type, plus optional payload occurrence/current-value fact. Payload occurrences have no independent incarnation, root location or governing-domain copy. Their existence is conditional on the installed variant having a payload; liveness implies a live enclosing root and live governing domain.

`SemanticValue` is either a sum or a loose payload value. Sum values contain variant, opaque payload content and canonical root/payload dependency partitions. Payload-only extraction uses a loose payload carrier rather than adding an independent installed carrier for the conditional subobject. Values own no source occurrence, place, incarnation or governing relation. Dependencies may reference exact source facts, which are obligations rather than identity ownership.

One fact vocabulary includes ordinary `F0.Fact`, `occurrence o`, and `payloadValue o vf`. The last distinguishes occurrence lifetime from the changing current payload value. One `LiveFacts` and one `DependenciesValid` check **every dependency of every surviving semantic carrier**, regardless of fact kind. There is no second sum-specific dependency validator or ad-hoc laundering prohibition. Payload dependencies join root dependencies only in a derived union, retaining their local partition for payload-only updates.

Persistent provenance is not automatically a dependency. Opaque payload content receives no implicit `OccurrenceFact`; occurrence dependence is explicit. The F0 ptr/ref model is unchanged. This does not claim a new pointer provenance or safe-ref derivation proof.

**Formal representation choices are non-normative.** The finite maps/sets, natural-number wrappers, content tokens and proof parameters are not compiler/runtime representation requirements.

## Historical freshness

`usedOccurrences` is proof-only ghost history. `FreshOccurrence s o` means `o` is absent from that entire history, not merely dead now. Occurrence 9 in a witness is retired but still cannot be allocated.

`Allocation` always allocates a fresh parent current fact. Its optional pair allocates a payload current fact and occurrence together, exactly when the incoming value has a payload. Both value facts exclude pre-history and differ internally. `FreshPair` requires pre-history freshness plus disjoint sets of value-fact and occurrence allocations, preventing the two destinations from choosing the same new ID.

Whole replace/store union allocation sets into history. Distinct swap unions both allocations atomically. Payload-only changes allocate fresh parent/payload current facts but retain occurrence history exactly. Same-place swap has no allocation parameter and changes neither history. Old identities remain recorded after becoming non-live. Initial snapshots must seed their full prior allocation histories; allocating transitions retain and extend those histories. This introduces no runtime occurrence counter and no new incarnation allocator.

## Transitions and results

| Operation | Parent / fixed identity | Occurrence | Old value carrier |
| --- | --- | --- | --- |
| Whole replace, including same variant | Preserved | Old ends; fresh new iff payload present | Old sum survives loose |
| Whole store | Preserved | Old ends; fresh new iff payload present | Old sum consumed atomically |
| Payload-only replace | Preserved | Preserved | Old payload survives loose |
| Payload-only store | Preserved | Preserved | Old payload consumed atomically |
| Same-place whole swap | Exact state identity | Unchanged | Unchanged |
| Distinct whole swap | Each destination identity preserved | Each old ends; destination fresh iff incoming payload present | Both sums survive at opposite places |

`wholeCandidate` directly constructs either combined replace or combined store endpoints. `RawWhole` contains structural/static premises, including whole-type Discardable only for store. Store is **not** defined by first requiring a legal replace and then discarding its result. At the visible value level, it resembles replacement whose old value is discarded; dependency legality belongs to the combined candidate.

`payloadCandidate` changes only the active payload semantic fragment and current facts, preserving the variant, root-local dependency partition, enclosing carrier, occurrence and static type table. Payload-only store requires the active payload **type's** Discardable capability, not whole-sum Discardable. Loose result IDs are uncarried before extraction. Ordinary surviving current-value dependencies remain subject to the same post invariant.

`RawSwap.same` contains live-target/write/type premises but no freshness supply. `RawSwapDistinct` constructs one atomic package exchange, without intermediate replace/take/initialize states. Package/dependency data and loose carriers stay identical. Old source occurrences do not travel with packages. There is no Copy, Discardable, exclusive-ref or lifetime-ending authority requirement for swap.

Legal `WholeStep`, `PayloadStep` and `SwapStep` require WellFormed pre, the raw relation, and WellFormed candidate post. Legal preservation is consequently a projection. Substantive laws are separately checked: exact target/frame equations, old occurrence death, historically fresh allocation/recording, carrier survival/consumption, unchanged dependency data, and generic survivor rejection. Concrete independently verified post-state witnesses rule out vacuity.

## Erasure/refinement strategy

`erase` forgets conditional precision and maps each modeled sum root to a singleton fixed layout in F1.1 `CurrentState`. It preserves root place/incarnation/current fact, governing domain, carriers, static whole-type capability, domains and existing histories. Ordinary dependencies are projected into actual installed/loose fragments; conditional facts and payload-current facts are forgotten. `erasure_retains_ordinary_package_dependencies` proves ordinary atom retention in the erased table.

`WellFormed` consists of structural/type/occurrence `Invariant` plus the single richer `DependenciesValid`. It does **not** assume erased CurrentWellFormed. `wellFormed_erases_to_currentWellFormed` constructs all F1.1 obligations, deriving ordinary dependency validity from the richer invariant. Thus `F1.2 WellFormed → F1.1 CurrentWellFormed (erase state)` is machine-checked.

This is a precision-losing **state** erasure, not exact Step simulation or full semantic value equivalence. The modeled slice has one opaque conditional payload under each sum lifetime root. Arbitrary fixed-aggregate embedding, multiple nested conditional occurrences and payload capability/match derivation are deferred; no existing F1.1 aggregate semantics is rewritten or weakened.

## Positive witnesses

All are Lean theorems in the isolated counterexample module:

- None → Some, Some → None, Some → same Some, and Some → a different payload variant are legal independent whole replacements.
- Returned old sum retains its payload value but the old occurrence is non-live; fresh same-variant occurrence is distinct from its old ID.
- From the same self-dependent state, whole replace rejects while whole store legally eliminates old-only occurrence dependency.
- Payload-only replace returns a self-occurrence-dependent old payload legally; payload-only store also preserves occurrence. The whole-versus-payload contrast is explicit.
- Same-place self-dependent sum swap is legal and exact identity.
- Independent distinct swap is legal; a second witness uses non-Discardable nominal sums.
- All incoming/external and left/right cross/self negative fixtures have separately checked WellFormed starting states; the cyclic and left-self states also have explicit checked pre-invariants.

## Negative controls and anti-laundering

- Returned old, incoming, and external-survivor occurrence dependencies reject whole updates. Store consumes only the dependency carried exclusively in the discarded old package.
- Left/right self, left/right cross, cyclic and third-survivor occurrence dependencies reject distinct swap. The same self dependency permits same-place swap.
- A cyclic raw candidate satisfies **all other invariants**, including carrier/place/incarnation/current-fact uniqueness, presence/typing, domain validity, occurrence shape/uniqueness and both history-recording obligations, but fails DependenciesValid. There is no special cyclic prohibition.
- Historical occurrence reuse and pair occurrence aliasing reject.
- Private broken candidates preserving old whole occurrence, reusing old occurrence in a same-variant update, moving occurrence IDs with packages, preserving source occurrences on distinct swap, refreshing occurrence in payload-only replace, or allocating on same-place swap violate the raw structural equations. Broken fresh occurrences are also entered into ghost history, so these controls do not rely on an unrecorded ID alone.
- A private candidate retargeting dependency atoms to fresh occurrences violates unchanged swap package data.
- A payloadless current variant can contribute true locally while its nominal sum type is non-Discardable. Both pre and combined candidate can be WellFormed, yet the omitted-static-capability store is not raw/legal. Applicability is not hidden in a state invariant.

These distinguish broken **raw operation conformance** from malformed **post dependency validity**; they are not counterexamples to the canonical legal rules.

## Formal findings and scope

- **FORMAL-ENCODING:** Use a nominal closed-sum root slice, explicit mixed facts, optional occurrence/current-value pair and ghost history. Occurrence is place-owned; transfer retains exact dependency references, never identity ownership. This is a small separately erased layer over the reviewed fixed model.
- **FORMAL-ENCODING:** Whole-type capability is derived across the closed variant set; payload-only capability comes from the payload type. Inert package records are permitted after carrier consumption.
- **FORMAL-LEMMA:** Parent/fixed identity survives while conditional occurrence ends/restarts; value transfer does not transfer occurrence; same-place is identity. Generic surviving-dependency rejection supplies replace/store/swap anti-laundering. The cyclic break-test isolates the necessity of the ordinary post invariant.
- **FORMAL-LEMMA:** Richer WellFormed implies F1.1 CurrentWellFormed via computed, precision-losing erasure with ordinary dependency retention.
- **FORMAL-SCOPE:** Opaque root-level sums only; no nested sum or arbitrary fixed-aggregate embedding, source syntax, constructor/match frontend, pattern/exhaustiveness checker, borrowed/consuming match, capability issuance, future-use scope analysis, source type checker, functions/callbacks/loops, physical layout, BackingRegion/Storage/slot/raw bytes, or relocation. Caller write/type obligations are abstract propositions, not semantic assumptions supplied by custom logic.

No **FORMAL-HOLE**, **FORMAL-AMBIGUITY** or new **FORMAL-EXTRACTION** was identified in the inspected canonical rules. §17.4 and §26 explicitly settle same-place no-op, distinct freshness, unchanged package dependencies and nontransfer of occurrence. No normative document is changed.

## Verification and CI

Lean/Lake **4.34.1**, elan **4.2.4**, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and all manifest/bootstrap/workflow pins are unchanged. No additional import cache closure or CI configuration is needed.

The existing 467 audit entries are retained in their original order. **100** F1.2 public declarations are added: **567** total. A project-clean `lake build` passed (**705 jobs**) and `bash scripts/check-proofs.sh` passed all **567** reports, with no Lean warnings. Project-owned Lean source contains no proof placeholders or custom semantic assumptions. Audited dependencies are only the existing whitelist: `propext`, `Classical.choice`, `Quot.sound` (or none).

The existing `Lean proofs` workflow builds and audits from fresh pinned toolchain/cache paths on push and pull_request. PR-triggered execution and the final-head run are recorded in the PR body after completion; CI confirmation is pending when this report is first committed. The PR remains open and unmerged for semantic review.

## Complete added audited declaration inventory

Names below use the namespace shown for each file. Private fixture lemmas are also kernel-checked by the build and are reached through these audited public declarations.

### NewLang/F1/Conditional/Counterexample/Sum.lean

Namespace: `NewLang.F1.Conditional.Counterexample.Sum`.

- `none_to_some_is_legal`
- `some_to_none_is_legal`
- `some_to_same_variant_is_legal`
- `different_payload_variants_is_legal`
- `independent_whole_replace_is_legal`
- `same_variant_whole_replace_restarts_occurrence`
- `whole_store_eliminates_old_only_occurrence_dependency`
- `whole_replace_rejects_old_only_occurrence_dependency`
- `occurrence_dependency_rejects_replace_but_allows_store`
- `same_place_sum_swap_is_exact_noop`
- `same_place_sum_swap_self_dependency_remains_live`
- `whole_incoming_occurrence_dependency_rejects_replace_and_store`
- `whole_external_occurrence_dependency_rejects_replace_and_store`
- `historically_used_but_dead_occurrence_is_not_fresh`
- `historical_occurrence_reuse_rejected`
- `current_variant_discardability_is_an_unsound_store_guard`
- `independent_distinct_sum_swap_is_legal`
- `nonDiscardable_sum_values_can_swap`
- `cyclic_swap_occurrence_laundering_rejected`
- `self_dependency_allows_same_swap_but_rejects_distinct`
- `left_cross_occurrence_swap_dependency_rejected`
- `right_self_occurrence_swap_dependency_rejected`
- `right_cross_occurrence_swap_dependency_rejected`
- `third_survivor_occurrence_swap_dependency_rejected`
- `cyclic_candidate_passes_all_other_invariants_but_fails_dependencies`
- `payload_only_replace_preserves_occurrence_with_self_dependency`
- `payload_only_store_preserves_occurrence`
- `whole_replace_preserving_old_occurrence_is_broken`
- `same_variant_whole_replace_reusing_old_occurrence_is_broken`
- `payload_only_replacement_allocating_occurrence_is_broken`
- `same_place_swap_allocating_occurrence_is_broken`
- `distinct_swap_preserving_source_occurrences_is_broken`
- `distinct_swap_transferring_occurrence_with_value_is_broken`
- `whole_value_result_preserves_payload_but_not_occurrence`
- `whole_vs_payload_only_occurrence_contrast`
- `omitting_static_sum_discardability_can_silently_lose_value`
- `reused_pair_occurrence_allocation_is_rejected`
- `all_negative_dependency_fixtures_have_wellFormed_pre_states`
- `rewriting_dependencies_to_fresh_occurrences_is_not_raw_swap`

### NewLang/F1/Conditional/Model.lean

Namespace: `NewLang.F1.Conditional`.

- `projectFacts_membership`
- `live_ordinary_fact_erases`
- `wellFormed_erases_to_currentWellFormed`
- `surviving_dependencies_are_live`
- `recorded_occurrence_is_not_fresh`
- `erasure_retains_ordinary_package_dependencies`

### NewLang/F1/Conditional/Proofs.lean

Namespace: `NewLang.F1.Conditional`.

- `fresh_allocation_cannot_reuse_occurrence`
- `allocation_occurrence_is_fresh`
- `whole_preserves_wellFormed`
- `whole_target_equation`
- `whole_preserves_parent_identity`
- `whole_preserves_static_frame`
- `whole_other_location_unchanged`
- `whole_new_package_installed`
- `whole_new_occurrence_equation`
- `whole_history_monotone`
- `whole_fresh_occurrence_recorded`
- `whole_fresh_current_facts_recorded`
- `whole_old_occurrence_ended`
- `whole_replace_old_package_survives`
- `whole_store_old_package_does_not_survive`
- `whole_incoming_no_longer_loose`
- `whole_store_requires_static_sum_discardability`
- `whole_store_rejects_nonDiscardable_sum`
- `whole_rejects_ended_occurrence_in_survivor`
- `whole_replace_rejects_returned_occurrence_dependency`
- `whole_rejects_incoming_occurrence_dependency`
- `whole_replace_value_transfers_without_occurrence`
- `payload_preserves_wellFormed`
- `payload_preserves_occurrence`
- `payload_preserves_parent_identity`
- `payload_installs_new_value`
- `payload_occurrence_dependency_remains_live`
- `payload_old_current_fact_dies`
- `payload_rejects_surviving_old_value_dependency`
- `payload_store_requires_static_payload_discardability`
- `swap_preserves_wellFormed`
- `swap_same_is_identity`
- `swap_same_preserves_variant_occurrence_history`
- `swap_distinct_target_equations`
- `swap_distinct_preserves_parent_identities`
- `swap_distinct_exchanges_values_without_rewriting_dependencies`
- `swap_distinct_preserves_frame`
- `swap_distinct_other_location_unchanged`
- `swap_distinct_both_packages_survive`
- `swap_distinct_fresh_occurrences_and_history`
- `swap_distinct_old_left_occurrence_ended`
- `swap_distinct_old_right_occurrence_ended`
- `swap_rejects_any_surviving_ended_occurrence`
- `swap_rejects_left_package_occurrence_dependency`
- `swap_rejects_right_package_occurrence_dependency`
- `whole_old_root_value_fact_ended`
- `whole_preserves_erased_fixed_identity`
- `whole_store_requires_all_possible_payload_types_discardable`
- `payload_fresh_facts_and_history`
- `payload_store_rejects_nonDiscardable_payload`
- `swap_distinct_two_current_facts_fresh_distinct_recorded`
- `live_occurrence_has_live_enclosing_root_and_domain`
- `conditional_payload_is_not_added_to_fixed_incarnation_support`
- `whole_new_occurrence_differs_from_old`
- `whole_payloadless_incoming_has_no_occurrence`

## Review handoff

F1.2 settles the two identity layers and occurrence-dependent survival for this explicitly bounded slice. **F1.2 IMPLEMENTATION COMPLETE / F1.2 READY FOR REVIEW.** After semantic review and merge, F1.3 BackingRegion/placement may start separately; this implementation makes no physical-memory safety claim.
