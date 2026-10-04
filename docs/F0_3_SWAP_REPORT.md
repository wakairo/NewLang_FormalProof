# F0.3 — swap report

Same-place swap changes nothing; distinct-place swap exchanges packages without retargeting their exact dependencies. This implements Draft 17.4 §13.5a / §17.4 and F0 bridge §16.

| Case | Current facts | Package carriers | Dependency legality |
| --- | --- | --- | --- |
| Same place | Unchanged; no allocation | Unchanged | Existing self-dependency remains valid |
| Distinct places | Both freshened; both old facts dead | Both survive at opposite locations | Surviving old-fact dependencies reject, including cyclic laundering |

The verified baseline is main merge commit `f6d550d`, with F0.0/F0.1/F0.2 and all 57 existing audited proofs. Draft 17.4, existing semantic modules/proofs, CI workflow, Lean/toolchain/manifest pins remain unchanged: Lean 4.34.1, elan 4.2.4, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Representation

`SwapCase` is a small swap-only sum. Its same constructor takes a location and root and has **no new-fact parameters**. `RawSwapSame` witnesses that root's liveness, both caller write premises, type agreement and exact equality `post = pre`. Every state field is preserved, including loose carriers and history. Any well-formed live same target satisfies the state part of legality, even when its package depends on its current fact.

The distinct constructor takes two locations/roots and two new facts. `RawSwapDistinct` records both live targets, distinct locations, both caller write premises, type agreement, historical freshness pair and equality with `swapCandidate`. Carrier uniqueness derives different installed PackageIds; place uniqueness derives different PlaceIds. Neither is smuggled into an extra raw package-inequality premise.

`FreshValueFactPair s a b := FreshValueFact s a ∧ FreshValueFact s b ∧ a ≠ b`. Two separately fresh IDs could coincide, so mutual inequality is essential. The candidate records `insert a (insert b pre.usedValueFacts)`, retains all old allocations and makes both new IDs current. This uses the existing proof-only history and does not prescribe runtime stamps/storage. The pair is a proof encoding of two fresh ghost allocations, not a compiler/runtime global stamp format. `usedIncarnations` is not added.

`swapCandidate` atomically updates exactly the two live roots. Places, locations, incarnations and place-owned governing domains stay at their original locations. Package IDs exchange; dependencies do not rewrite. Both old packages survive installed at the opposite roots. Package-table data, loose carriers, live domains and every other location are unchanged. The unit result has no package carrier. There is no observable intermediate state, sequential replace, or take/initialize encoding.

`RawSwap` dispatches these two cases; `SwapStep := WellFormed pre ∧ RawSwap ∧ WellFormed post`. `SwapSameStep` / `SwapDistinctStep` abbreviate the cases. Distinct preservation intentionally projects the post-state legality condition; update, frame, freshness, invalidation, survival and rejection theorems prove the substantive facts separately. No claim asserts that all raw candidates are legal.

**F0.3 does not introduce a Copy requirement.** It requires no Discardable, exclusive reference, or LifetimeDomain/lifetime-ending authority. The caller write/type propositions remain abstract; True is supplied only by isolated fixtures. Source-level ref derivation and type/borrow checking are outside the model.

## Why laundering rejects

Both packages and every other survivor remain tracked. Both old exact value facts disappear from LiveFacts. The package table (including dependencies) is unchanged. Therefore any post survivor carrying either old fact contradicts ordinary DependenciesValid. Self, cross, cyclic and third-survivor cases all specialize that argument; there is no swap-specific ad-hoc rejection rule.

The concrete fixture has two live roots with different place/incarnation/domain IDs, installed packages A/B, a third loose package Q, and a retired recorded fact. Dependencies can refer to either old fact; all fixture inputs used here are well formed initially. All packages are non-discardable.

- Independent distinct swap is legal, including with both installed values non-discardable.
- The same self-dependent pre-state permits same-place swap and rejects distinct swap.
- Left/right self dependencies and left/right cross dependencies reject every candidate legal distinct step.
- Cyclic `A → old B`, `B → old A` rejects even though both packages move to the dependency's place; old identities never become the new current identities.
- A third loose survivor depending on either old fact rejects (both sides checked).
- A cyclic raw candidate satisfies CarrierUnique, PlacesUnique, IncarnationsUnique, PackagesPresent, DomainsValid and ValueFactsRecorded but fails DependenciesValid alone.
- Retired IDs are currently dead but rejected for either allocation position. A historically unused ID reused for both new allocations also rejects.

Broken dependency validation is demonstrated only in the isolated counterexample namespace. Production legality remains unchanged.

## Machine-checked inventory

All 45 new public declarations below are audited with `#print axioms`; existing 57 remain audited as well.

Namespace `NewLang.F0`:

| Theorem | Checked property |
| --- | --- |
| `swap_same_is_identity` | Exact state identity |
| `swap_same_preserves_history` | No history allocation/change |
| `swap_same_preserves_current_fact` | Current fact unchanged |
| `swap_same_preserves_package` | Installed package unchanged |
| `same_swap_is_legal` | Well-formed live same target is legal with caller premises |
| `RawSwapDistinct.targets_after` | Exact two target updates |
| `RawSwapDistinct.packages_distinct` | Different installed packages from carrier uniqueness |
| `RawSwapDistinct.places_distinct` | Different places from place uniqueness |
| `swap_distinct_preserves_wellFormed` | Legal post-state invariant |
| `swap_distinct_preserves_incarnations` | Both incarnations preserved |
| `swap_distinct_preserves_governingDomains` | Both place-owned domains preserved |
| `swap_distinct_preserves_places_and_locations` | Both places/locations/live status preserved |
| `swap_distinct_exchanges_packages` | Installed carriers exchanged |
| `swap_distinct_both_packages_survive` | Both old packages survive at opposite locations |
| `swap_distinct_preserves_loose_packages` | Loose carrier set unchanged |
| `swap_distinct_preserves_package_data_and_domains` | Table/dependencies and live domains unchanged |
| `swap_distinct_preserves_other_locations` | Frame outside both targets |
| `swap_distinct_history_monotone` | All allocation history retained |
| `swap_distinct_creates_two_fresh_current_facts` | Historical freshness, mutual inequality, current facts, recording and history inclusion |
| `swap_distinct_old_facts_remain_used` | Both old allocated identities remain recorded |
| `swap_distinct_survivors_preserved` | Every pre-survivor remains tracked |
| `rawSwapDistinct_old_left_fact_not_live` | Exact old left fact dead |
| `rawSwapDistinct_old_right_fact_not_live` | Exact old right fact dead |
| `swap_rejects_surviving_old_current_dependency` | Any survivor carrying either old fact rejects |
| `swap_rejects_left_self_current_dependency` | Left self-dependency rejects |
| `swap_rejects_left_package_cross_dependency` | Left package dependency on old right rejects |
| `swap_rejects_right_self_current_dependency` | Right self-dependency rejects |
| `swap_rejects_right_package_cross_dependency` | Right package dependency on old left rejects |
| `swap_rejects_reused_left_fact` | Left historical reuse rejects RawSwapDistinct |
| `swap_rejects_reused_right_fact` | Right historical reuse rejects RawSwapDistinct |
| `swap_rejects_colliding_new_facts` | Two new allocations cannot coincide |

Namespace `NewLang.F0.Counterexample.Swap`:

| Theorem | Checked property |
| --- | --- |
| `before_wellFormed` | All used dependency fixtures start well formed |
| `independent_distinct_swap_is_legal` | Concrete legal distinct witness |
| `swap_does_not_require_discardable` | Both installed packages have discardable=false |
| `same_place_swap_preserves_self_dependency` | Concrete legal same/self-dependent witness |
| `left_self_dependency_is_rejected` | Concrete left self rejection |
| `right_self_dependency_is_rejected` | Concrete right self rejection |
| `left_cross_dependency_is_rejected` | Concrete left cross rejection |
| `right_cross_dependency_is_rejected` | Concrete right cross rejection |
| `self_dependency_allows_same_swap_but_rejects_distinct_swap` | Same pre-state, contrasting operations |
| `swap_rejects_cyclic_dependency_laundering` | Concrete cyclic laundering rejection |
| `third_survivor_left_dependency_is_rejected` | Third package old-left dependency rejection |
| `third_survivor_right_dependency_is_rejected` | Third package old-right dependency rejection |
| `unchecked_cyclic_swap_breaks_dependencies` | Every other invariant passes; dependency validity fails |
| `historical_reuse_and_pair_collision_are_rejected` | Dead recorded identity reuse and fresh pair collision reject |

## Validation, findings and next step

Required branch validation:

```bash
lake build
bash scripts/check-proofs.sh
```

The checker scans all project-owned Lean modules for placeholders/custom declarations and audits **102 theorem reports** (57 existing + 45 F0.3). Only standard `propext`, `Classical.choice`, and `Quot.sound` are allowed. No semantic shortcuts are introduced. Root imports build production and counterexample modules together.

The existing pinned `Lean proofs` workflow is reused unchanged on push and pull_request. Work uses `f0.3-swap`, an open PR targeting main, and verification of the pull_request-event run for the branch commit. CI results are recorded on the PR; success does not merge it.

- **FORMAL-ENCODING:** Swap-only case sum, exact same identity, historical fresh pair, distinct location/place correspondence and unchanged package data are non-normative proof choices.
- **FORMAL-LEMMA:** Survival plus both old-fact invalidations makes ordinary DependenciesValid sufficient to reject every laundering case; concrete positive witnesses exclude vacuous legality.
- **FORMAL-SCOPE:** Only swap was added. Existing F0.0/F0.1/F0.2 code is unchanged; no F0.4+, incarnation history, structural/aggregate/sum semantics or general transition/allocator framework was introduced.
- No new **FORMAL-HOLE**, **FORMAL-AMBIGUITY**, or **FORMAL-EXTRACTION** issue was found. Draft 17.4 §17.4 specifies exact same-place no-op and complete package/hidden-dependency transfer; §13.5a supplies exact fact tracking and dependency survival. The fresh pair is the permitted ghost-identity encoding, not a normative implementation constraint. The previous resolved milestone-number correction remains in the notes.

After semantic/formalization review and merge, the foundation is ready for F0.4 — initialize / take / destroy. This will require incarnation allocation history and new lifetime-specific premises; they are deliberately not implemented here.
