# F1.1 — Fixed Subobject / Structural Current-State Transitions

## Representation audit and reviewed baseline

**NO: F1.0's flat loose ValuePackage alone is insufficient.** Its dependency union
cannot recover which relative child owned an atom after an aggregate is returned
and reinstalled. F1.1 therefore adds a conservative layer, rather than replacing
the reviewed scaffold:

- `CurrentState.base : F1.State` retains the entire F1.0 model.
- `content location place : Nat` is an opaque **local semantic fragment token**.
  Nat is a proof encoding, not NewLang's value domain, representation or ABI.
  An aggregate's complete value consists of its supported relative fragments;
  an ancestor's own fragment need not change when one child changes.
- `capability location place : Bool` records the fixed type's Discardable capability.
  All operations preserve this map; it is not a payload-dependent runtime property.
- `carried PackageId : Option StructuredValue` holds structured loose values.
  A StructuredValue has finite **value-relative** path support, per-position content
  and exact dependencies, and per-position static capability bits.
- `CurrentWellFormed` requires the existing thirteen F1 invariant fields, a structured
  value/flat summary correspondence for every loose carrier, and agreement between
  the root's capability and its reviewed root discardability field.

A carried value has no source PlaceId/incarnation/placement/governing metadata.
A dependency atom may still mention a PlaceId as its **dependency referent**; this
is necessary exact-fact identity, not transferred place ownership. Paths in a layout
are place coordinates; paths in a carried value are relative semantic positions.
Neither is source syntax or a byte offset. Content can abstract identity/authority/
provenance-bearing value components, but their internal algebra is not proved here.

`extract_value_fragment` proves exact extraction of content, LocalDeps and type
capability at every supported relative position. `relative_positions_injective`
uses the reviewed tree's path injectivity. `extract_value_dependencies` proves that
the summary is exactly SubtreeDeps. Private broken extraction/flattening controls
show a child obligation would otherwise disappear.

F1.0 PR #6 passed review and merged at main
`fdda0d99d3de961f782f465fa2033b5554790ba5`. Before changes, this exact main passed
`lake clean newlang-formal`, `lake build` (694 jobs) and all **332** audits.
All F0 semantic sources and all F1.0 Lean definitions/theorems remain byte-for-byte
unchanged. F0 remains CLOSED; F1.0 remains CLOSED/MERGED. This branch implements
F1.1 for review and does not merge it.

## Authority and inspected rules

The canonical language specification is selected by `docs/reference/CURRENT_SPEC.md`
on `wakairo/NewLang_Compiler` `main`; at final review it points to Draft 17.6.
The local Draft 17.4 file remains an unchanged historical snapshot with SHA-256
`a552468ec3d96a79d17495fb251f63475c752ee0a8ee1e1ffa5bf9a887818c12`.

For the F1.1 scope, Draft 17.6 §3.8 / §13.5a / §17.4 were compared directly with
the local Draft 17.4 snapshot and are byte-for-byte identical. Draft 17.5's
exclusive-reborrow clarification and Draft 17.6's raw-Storage byte bridge do not
change fixed-subobject replace/store/swap semantics.

The F0 bridge remains non-normative; this layer is proof encoding. Inspected rules
include §3.5's same-or-disjoint typed referents, §3.6/§3.8's fixed-subobject lifetime
relation, §13.5a's current-value overlap and smallest-subvalue dependency ownership,
and §17.4's complete-value transfer, atomic store, same-place swap and fixed aggregate
rules. §26 was read only to check that fixed-support helpers do not claim conditional
occurrence semantics. Backend/physical-layout and source-surface authority are not
expanded in this task. No new normative rule or adjudication is invented.

**Formal representation choices are non-normative.** The ghost sets, coordinate
functions, carrier IDs, tokens, capability bits and classical selection functions
are not compiler/runtime storage requirements.

## Affected facts and lifetime identity

`liveNodeSupport` enumerates supported `(location, place)` pairs. `affectedBy` filters
that support by target location and StructuralOverlap. `swapAffected` is the union
of both targets' sets. KnownDisjoint alone supplies no authority: raw relations
require LiveNode targets, and framing theorems explicitly carry live/tracked premises.

| Node relative to replace/store target | Current fact | Local semantic fragment | Incarnation |
| --- | --- | --- | --- |
| Target | Fresh | Incoming relative root fragment | Preserved |
| Descendant | Fresh | Incoming matching relative fragment | Preserved |
| Strict ancestor | Fresh | Own content/LocalDeps preserved | Preserved |
| Known-disjoint live node | Preserved | Preserved | Preserved |
| Other live root | Preserved | Preserved | Preserved |

`FreshStructuralFacts pre support supply` requires every supplied fact to be absent
from **all prior allocation history**, plus injectivity on the affected support.
The post history is `pre.usedValueFacts ∪ support.image supply`. Old identities are
never removed. Incarnation history is unchanged. A shared swap ancestor appears
once in a Finset union and receives one new fact, rather than two allocations.

The substantive proofs establish target/ancestor/descendant membership, exact fact
equations, pairwise uniqueness, allocation recording, history monotonicity, old-fact
non-liveness, and disjoint old-fact liveness. Freshness plus pre-state place uniqueness
rules out another root resurrecting an affected exact old fact. Currently dead
history IDs remain unavailable.

All layouts, tracked place support, path/parent/overlap relations, root locations,
fixed incarnations, live domains, domain carriers and place-side governing relations
are preserved. Child domains are never copied or transferred. These statements
are specific to fixed-shape lifetime-preserving transitions, not future occurrence
or relocation transitions.

## Candidates, relations and carriers

Each candidate is a pure, simultaneous transformation. Legal steps are
`CurrentWellFormed pre ∧ Raw operation ∧ CurrentWellFormed post`.
Write/type premises are caller-supplied propositions that require proofs; they are
not universally True in production. FitsTarget checks shape and static capability
agreement independently. No exclusive or lifetime-ending authority is introduced.

### Replace

`installValue` installs the incoming fragments only within the target subtree,
refreshes all overlap facts and consumes the incoming loose carrier.
`structuralReplaceCandidate` additionally installs the **entire extracted old value**
as a loose result, with both precise structured data and its checked flat summary.
`RawStructuralReplace` checks live target, incoming availability/value equality,
shape/type agreement, result carrier identity/availability and fresh allocation.

For a whole-root target, the result ID is the old root carrier and the incoming ID
becomes the root carrier. For a fixed child, the enclosing root carrier is retained;
a separate currently uncarried result ID holds the extracted child/subaggregate.
It is never treated as the old complete root package. Ancestors' own LocalDeps remain
and can themselves reject the transition if they depend on an invalidated fact.

`replace_old_value_survives`, `replace_installs_complete_structured_value` and
`replace_consumes_incoming_loose_carrier` establish the complete flow. A returned
old package cannot shed a child-local dependency. Returned, incoming and external
survivor dependencies on affected old facts reject through ordinary post invariants.

### Store

`structuralStoreCandidate` directly uses the same installation/fact change; it adds
**no result carrier**. `RawStructuralStore` additionally requires
`pre.capability target.location target.place = true`. Whole-root carrier consumption
is proved separately; child old fragments are atomically replaced inside their
existing root carrier, without inventing independent child package IDs.

At the visible value level, store behaves like replacement whose old value is
discarded. **For dependency legality, store is one combined transition. It is not
“first require a legal ReplaceStep, then discard its result.”** Inert carried/table
records without loose carriers are not survivors and need not be physically deleted.

A concrete old-only self-dependency admits leaf, nested and whole-root store and
rejects comparable replace. Incoming and external surviving dependencies still reject.
Root discardability cannot authorize a non-discardable child: a well-formed fixture
has a discardable root and a non-discardable child. Another break-test shows that
omitting the guard admits a well-formed candidate that silently loses a
non-discardable old value. Thus applicability is separate from state invariants.
No destructor/Drop model is introduced. Incoming capability metadata describes the
same fixed type; there is no separate runtime discardability test on its payload.

### Swap

`RawStructuralSwap.same` contains **no fresh supply parameter** and requires exact
post/pre state identity. Its self-dependent fixture is legal, with unchanged facts,
LocalDeps, content, carriers, histories, layout, incarnations and domains.

`RawStructuralSwapDistinct` requires live targets, structural disjointness, compatible
relative shapes/capabilities, caller write/type proofs and a fresh map over the union.
Distinct roots are separate structural trees; distinct targets inside one root must
be KnownDisjoint. Ancestor/descendant targets are inapplicable. This encodes the typed
same-or-disjoint boundary without proving physical byte geometry.

`structuralSwapCandidate` extracts both **pre-state** complete subtrees and exchanges
fragments by matching relative positions. It does not implement sequential replace,
take or initialize. Common ancestors' own LocalDeps remain; both target subtrees'
old fragments survive at the opposite targets. Dependencies retain exact old Fact
identities and never retarget. The loose carrier/table and domain data are unchanged.
When both targets are whole roots, root package carrier IDs exchange; for subobject
exchange, enclosing composite carrier IDs remain place-owned.

`swap_distinct_exchanges_complete_structured_values` proves both directions for
content, dependencies and static capability correspondence. Aggregate witnesses
prove A.x content moves to B.x while A.x's incarnation stays at A.x. Self, cross/
cyclic and third-survivor old-fact dependencies reject solely by candidate dependency
validity. Dependencies on an unaffected external sibling admit a concrete swap.
Both independent leaf and aggregate witnesses use non-discardable values.
**F1.1 does not introduce a Copy requirement.** No Discardable or lifetime-ending
premise is added to swap.

## Erasure and F0 consistency

The reviewed `f1_wellFormed_erases_to_f0_wellFormed` is retained with exactly its
original statement and proof. Each legal operation's post-state erases to a
well-formed F0 state. Installed local obligations still use the reviewed
`erase_local_dependency_obligation`; loose carried dependencies use their exact
flat summary. `carried_structured_dependency_is_retained_by_erasure` proves that
every such obligation appears in the **actual erased package table**, not merely
that its erased atom is live.

Whole-root replace/store use the existing root carrier/result/consumption behavior;
a concrete two-root swap retains different governing domains and incarnations and
exchanges the carriers. Root fact/incarnation/domain observations follow eraseRoot;
all ghost histories include old and newly allocated child identities.

No F1-step iff F0-step claim is made. The erasure widens a preserved child fact to
the enclosing **new** root fact when another child changes. Its precision loss and
derived table summaries make literal F0 RawStep equality inappropriate for general
subobject operations. The sanity claims are well-formed erased endpoints, preserved
root identity/domain observations, root fact changes and conservative obligations.

## Concrete evidence and deliberately broken rules

The main fixture has two same-shaped aggregates plus an external sibling:

```text
Root
├── left
│   ├── x
│   └── y
├── right
│   ├── x
│   └── y
└── external
```

| Evidence | Machine-checked result |
| --- | --- |
| replace(left.x) | root/left/x fresh; left.y/right/external framed |
| replace(left) | root/left/x/y fresh; right/external framed |
| replace(root) | All supported current facts fresh; all incarnations retained |
| Old/new dependency on disjoint right | Legal replace; incoming dependency stays child-local |
| Old self-dependency | Replace rejects; atomic leaf/nested/root store accepts |
| Incoming dependency on old target | Replace and store reject |
| External/ancestor local dependency on old target | Store/replace reject |
| same-place self-dependent swap | Exact no-op is legal |
| Distinct self-dependent swap | Rejected for the same pre-state |
| Independent sibling/aggregate swap | Legal without Discardable; relative children exchange content |
| Cyclic old cross-dependencies | Raw candidate exists; legal candidate rejects |
| Third-survivor dependency | Distinct swap rejects |
| Dependency on unaffected external sibling | Legal distinct swap |
| Shared ancestors | Finite union allocates once per ancestor; external fact retained |
| Two whole roots | Legal swap; carriers exchange, domains/incarnations remain |
| Missing ancestor invalidation | Broken candidate is not RawStructuralReplace |
| Missing descendant invalidation | Broken aggregate candidate is not RawStructuralReplace |
| Incarnation refresh | Broken candidate is not RawStructuralReplace |
| Sibling over-invalidation | Turns an otherwise legal replace into an invalid survivor state |
| Dropped old child dependency / flattened incoming | Exact fragment obligation is lost; original structured value differs |
| Non-discardable child / discardable parent | RawStore rejects based on child capability |
| Omitted discardability check | Post can be well formed despite forbidden consumption |
| Same-place fresh allocation | Broken candidate cannot inhabit the no-op relation |
| Ancestor/descendant swap | Structural disjointness premise cannot hold |
| Recorded historical ID reuse / new-ID aliasing | FreshStructuralFacts rejects |

Deliberately broken transforms (`patchFact`, `patchIncarnation`, `dropFragments`) are
private to Counterexample modules, not production kernel alternatives. Missing
ancestor/descendant refresh is an operation-conformance failure even if state-only
WellFormed can hold; sibling over-invalidation is unnecessary rejection, not a false
memory-unsafety claim. Preservation theorems project the legal post invariant; the
substantive construction, framing, extraction and non-laundering facts are separately
proved and the legal witnesses exclude vacuous legality.

## Validation, pins and workflow

Baseline: 332 previous audits, all retained in their original order. F1.1 adds
**135** audited public declarations: **92** production/helper facts and **43**
concrete controls, for **467** total. Private proof helpers are included transitively
in the public theorem dependency audit. No project-owned semantic proof placeholder
or custom assumption is accepted. The whitelist remains only `propext`,
`Classical.choice`, `Quot.sound` (or no dependencies).

Final local gate:

```bash
export ELAN_HOME=/workspace/.local/elan
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR=/workspace/.cache/mathlib
lake clean newlang-formal
lake build
bash scripts/check-proofs.sh
```

The project build checks 701 jobs including all earlier milestones and both new
counterexample modules. Lean/Lake `4.34.1`, elan `4.2.4`, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, all manifest revisions, bootstrap/checksums,
cache import closure (655 modules) and GitHub Actions workflow are unchanged.
CI runs the existing pinned bootstrap on fresh runner-temporary directories.

Branch: `f1.1-fixed-subobject-transitions`, base main
`fdda0d99d3de961f782f465fa2033b5554790ba5`. An open PR targets main; it is not merged
by this task. The final PR body and task completion report record the actual current
head SHA and its successful **pull_request-event** `Lean proofs` run URL. Keeping
that GitHub-generated metadata outside the source commit avoids a recursive head
SHA/update cycle. An older intermediate green run is insufficient.

## Findings and next milestone

| Classification | F1.1 finding |
| --- | --- |
| FORMAL-ENCODING | Flat loose values are insufficient; add conservative structured carrier/content/capability layer, relative fragment extraction, overlap support and injective historical fresh map |
| FORMAL-LEMMA | Exact fragment/summary conservation, overlap invalidation and sibling framing, atomic survivor analysis, root carrier distinction and same/distinct swap contrast |
| FORMAL-SCOPE | Precision-losing F0 state erasure is sanity refinement, not exact Step equivalence; fixed support only; type/write derivations and opaque payload algebra remain caller/abstraction boundaries |
| FORMAL-HOLE | None found in the inspected rules |
| FORMAL-AMBIGUITY | None found: §13.5a and §17.4 support complete fragment transfer, overlap updates, unchanged exact dependencies and static Discardable applicability |
| FORMAL-EXTRACTION | No new extraction error; resolved F0 milestone-number history is retained |

F1.1's implementation gate is the local proof/audit success plus current-head PR CI.
Semantic closure awaits human/ChatGPT review; the PR remains unmerged. F1.2 can start
**after that review**, with conditional occurrence support handled separately.
No OccurrenceId, sum transition, BackingRegion/ByteRange, Storage/slot, relocation,
lexical ref future-use, function boundary, concurrency or source syntax is implemented.
No whole-language type/memory safety or compiler correctness is claimed.

## Complete audited F1.1 declaration inventory

All names below are newly audited; existing 332 names remain unchanged.

### [StructuralValue.lean](../NewLang/F1/StructuralValue.lean) — 6

Namespace: `NewLang.F1`.

- `below_path_decomposition`
- `relative_positions_injective`
- `extract_value_fragment`
- `extract_value_dependencies`
- `carried_dependency_survives_erasure`
- `carried_structured_dependency_is_retained_by_erasure`

### [CurrentFacts.lean](../NewLang/F1/CurrentFacts.lean) — 14

Namespace: `NewLang.F1`.

- `mem_live_node_support`
- `mem_affectedBy`
- `target_is_affected`
- `ancestor_of_target_is_affected`
- `descendant_of_target_is_affected`
- `known_disjoint_live_node_is_not_affected`
- `refresh_current_fact`
- `refresh_history_monotone`
- `refresh_records_new_facts`
- `fresh_structural_facts_reject_reuse`
- `fresh_structural_facts_reject_aliasing`
- `refreshed_old_fact_not_live`
- `refreshed_current_facts_unique`
- `refreshed_current_facts_recorded`

### [Replace.lean](../NewLang/F1/Replace.lean) — 25

Namespace: `NewLang.F1`.

- `replace_preserves_wellFormed`
- `replace_post_erases_to_wellFormed_f0`
- `replace_preserves_layout`
- `replace_preserves_all_incarnations`
- `replace_preserves_governing_domain`
- `replace_preserves_fixed_support_and_incarnation_history`
- `replace_current_fact_equation`
- `replace_freshens_affected`
- `replace_freshens_target`
- `replace_freshens_ancestors`
- `replace_freshens_descendants`
- `replace_preserves_known_disjoint_current_facts`
- `replace_history_monotone`
- `replace_old_affected_facts_not_live`
- `replace_preserves_disjoint_live_facts`
- `replace_old_value_survives`
- `replace_installs_new_value`
- `replace_preserves_local_fragments_outside_target`
- `replace_rejects_old_result_invalidated_dependency`
- `replace_rejects_incoming_invalidated_dependency`
- `replace_installs_complete_structured_value`
- `replace_consumes_incoming_loose_carrier`
- `replace_preserves_enclosing_root_carrier_for_subobject`
- `replace_root_carrier_becomes_incoming`
- `replace_rejects_other_surviving_invalidated_dependency`

### [Store.lean](../NewLang/F1/Store.lean) — 21

Namespace: `NewLang.F1`.

- `store_preserves_wellFormed`
- `store_post_erases_to_wellFormed_f0`
- `store_preserves_all_incarnations`
- `store_preserves_layout_and_governing_domain`
- `store_requires_target_discardable`
- `store_rejects_nondiscardable_target`
- `store_same_structural_change_set_as_replace`
- `store_current_fact_equation`
- `store_freshens_affected`
- `store_history_monotone`
- `store_preserves_capability_and_incarnation_history`
- `store_old_value_does_not_survive_as_result`
- `store_old_root_carrier_does_not_survive`
- `store_installs_new_value`
- `store_preserves_local_fragments_outside_target`
- `store_preserves_known_disjoint_state`
- `store_old_affected_facts_not_live`
- `store_rejects_other_surviving_invalidated_dependency`
- `store_rejects_incoming_invalidated_dependency`
- `store_preserves_enclosing_root_carrier_for_subobject`
- `store_root_carrier_becomes_incoming`

### [Swap.lean](../NewLang/F1/Swap.lean) — 26

Namespace: `NewLang.F1`.

- `disjoint_targets_are_distinct`
- `swap_same_is_identity`
- `swap_same_consumes_no_fresh_fact`
- `swap_preserves_wellFormed`
- `swap_post_erases_to_wellFormed_f0`
- `swap_distinct_requires_disjoint_targets`
- `swap_distinct_preserves_all_incarnations`
- `swap_distinct_preserves_layout_and_governing_domains`
- `swap_distinct_preserves_carriers_and_domains`
- `swap_distinct_current_fact_equation`
- `swap_distinct_creates_fresh_current_facts`
- `swap_distinct_history_monotone`
- `swap_distinct_new_fact_ids_are_pairwise_distinct`
- `swap_distinct_preserves_unaffected_current_facts`
- `swap_distinct_old_affected_facts_not_live`
- `swap_distinct_installs_right_value_at_left`
- `disjoint_subtrees_have_no_common_node`
- `swap_right_subtree_is_outside_left`
- `swap_distinct_installs_left_value_at_right`
- `swap_distinct_exchanges_complete_structured_values`
- `swap_preserves_external_disjoint_state`
- `swap_rejects_right_value_old_fact_dependency`
- `swap_rejects_left_value_old_fact_dependency`
- `swap_preserves_local_fragments_outside_targets`
- `swap_rejects_external_surviving_invalidated_dependency`
- `swap_whole_root_carriers_are_exchanged`

### [Transition.lean](../NewLang/F1/Counterexample/Transition.lean) — 41

Namespace: `NewLang.F1.Counterexample.Transition`.

- `leaf_replace_is_legal`
- `nested_aggregate_replace_is_legal`
- `whole_root_replace_is_legal`
- `leaf_replace_freshens_root_left_leaf_and_frames_siblings`
- `nested_replace_freshens_descendants_and_preserves_right`
- `whole_root_replace_freshens_all_fixed_nodes`
- `store_eliminates_old_only_structural_dependency`
- `nested_store_eliminates_old_only_dependency`
- `replace_rejects_old_self_structural_dependency`
- `old_self_dependency_rejects_structural_replace_but_allows_store`
- `incoming_old_structural_fact_rejects_replace_and_store`
- `external_survivor_dependency_rejects_store`
- `nondiscardable_fixed_child_rejects_store`
- `independent_distinct_fixed_swap_is_legal`
- `fixed_swap_does_not_require_discardable`
- `same_place_self_dependency_is_legal`
- `cyclic_structural_swap_laundering_is_rejected`
- `whole_root_store_is_legal`
- `disjoint_dependency_replace_is_legal`
- `incoming_dependency_partition_is_preserved`
- `missing_ancestor_invalidation_is_not_replace`
- `missing_descendant_invalidation_is_not_replace`
- `incarnation_refresh_is_not_replace`
- `same_place_swap_cannot_allocate_facts`
- `ancestor_descendant_swap_is_inapplicable`
- `previously_used_dead_fact_cannot_be_reallocated`
- `duplicated_new_structural_fact_is_rejected`
- `returned_value_must_retain_child_local_dependency`
- `flattened_incoming_package_loses_child_obligation`
- `incoming_flattening_is_not_the_original_value`
- `overinvalidating_sibling_rejects_an_otherwise_legal_replace`
- `independent_aggregate_sibling_swap_is_legal`
- `aggregate_swap_exchanges_child_values_without_exchanging_incarnations`
- `self_dependency_allows_same_swap_but_rejects_distinct_swap`
- `cyclic_candidate_without_dependency_check_is_malformed`
- `swap_preserves_external_disjoint_dependency_witness`
- `third_survivor_rejects_structural_swap`
- `sibling_swap_freshens_shared_ancestors_once_and_frames_external_sibling`
- `root_discardability_cannot_authorize_child_store`
- `ancestor_local_dependency_is_preserved_and_rejects_replace`
- `omitting_discardability_can_silently_lose_nondiscardable_value`

### [RootTransition.lean](../NewLang/F1/Counterexample/RootTransition.lean) — 2

Namespace: `NewLang.F1.Counterexample.RootTransition`.

- `whole_root_swap_is_legal`
- `whole_root_swap_erasure_observations`
