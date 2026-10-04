# F0.2 — atomic store report

F0.2 proves the survivor distinction in Draft 17.4 §13.5a / §17.4 and F0 bridge §15:

| Operation | Old carrier after transition | Old-only dependency on the invalidated fact |
| --- | --- | --- |
| replace | Survives as loose result | Rejects |
| store | Consumed; no surviving carrier | Can be legal when old value is discardable |

Draft 17.4, Lean 4.34.1, elan 4.2.4, the mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` pin and the dependency manifest are unchanged. Existing F0.0/F0.1 statements and proofs remain unchanged and checked.

## Transition encoding

`storeCandidate` performs a single update to the target's current fact and installed package. It preserves place, location, incarnation, governing domain, live-root status, all other locations, live domains and package-table data. Loose carriers become `(pre.loosePackages.erase incoming).erase old`. History becomes `insert newFact pre.usedValueFacts`.

`RawStore` requires the target live root, incoming loose carrier, historically fresh new fact, caller-supplied write/type propositions, an existing old package with `discardable = true`, and equality with the candidate. `StoreStep` requires well-formed pre-state, `RawStore`, and well-formed post-state. The unit result has no value-package carrier; no extra result datatype is needed.

At the visible value level, store behaves like replacement whose old value is discarded. **For dependency legality, store is one combined transition. It is not defined as “first require a legal ReplaceStep, then discard its result.”** Otherwise the legal old-only-dependency example below would be incorrectly rejected.

Discardability is the existing Boolean proof-side static abstraction, not a runtime check. Only the old package needs it; incoming discardability is not checked. Caller propositions remain abstract production obligations, with True used only in fixtures to isolate state semantics. No exclusive reference, lifetime-ending authority, destructor or Drop semantics is introduced.

Old table data remains available but has no carrier. `Survives` depends on carriers, not table presence. Pre-state carrier uniqueness excludes incoming = old and other old installations; all old carriers are consumed, while every other survivor remains tracked. This representation does not impose physical table retention/deletion on a compiler/runtime.

Historical freshness reuses `usedValueFacts`, `FreshValueFact` and `ValueFactsRecorded` without modification. The new identity was never previously allocated in the seeded model history, is recorded afterward, and every earlier identity remains used. A dead recorded identity still cannot be reused. The set remains proof-only ghost state; `usedIncarnations` is not implemented.

## Machine-checked inventory

The production names below are in `NewLang.F0`:

| Theorem | Property |
| --- | --- |
| `RawStore.target_after` | Exact target root update |
| `RawStore.packages_unchanged` | Package-table preservation |
| `RawStore.incoming_ne_old` | Pre-state uniqueness separates loose incoming and installed old |
| `RawStore.newFact_ne_old` | Historical freshness changes the current fact |
| `store_preserves_wellFormed` | Legal post-state invariant (projection of legality) |
| `store_preserves_incarnation` | Same incarnation |
| `store_preserves_governingDomain` | Same governing domain |
| `store_preserves_place_and_location` | Same place, location and live-root status |
| `store_preserves_other_locations` | Frame for every other location |
| `store_preserves_package_data_and_domains` | Unchanged package table and live-domain set |
| `store_creates_fresh_current_fact` | Fresh in pre-history, recorded in post-history and current at target |
| `store_history_monotone` | All prior history retained |
| `store_old_fact_remains_used` | Invalidated old identity remains allocated |
| `store_new_package_installed` | Incoming installed and no longer loose |
| `rawStore_old_package_does_not_survive` | Old carrier consumption from well-formed pre-state and raw transition |
| `store_old_package_does_not_survive` | No surviving old carrier after legal store |
| `store_other_survivors_preserved` | Every survivor other than old remains tracked |
| `rawStore_old_current_fact_not_live` | Old current fact dead in candidate |
| `store_rejects_other_surviving_old_current_dependency` | Any other pre-survivor carrying the old dependency rejects |
| `store_rejects_incoming_old_current_dependency` | Incoming old-current dependency rejects |
| `store_requires_discardable_old_package` | Legal step includes the old discardability premise |
| `store_rejects_nondiscardable_old_package` | Non-discardable old value prevents even RawStore |
| `store_rejects_previously_used_fact` | Previously allocated identity prevents RawStore |

The preservation theorem intentionally projects post-state legality. It does not assert all raw candidates are legal. The carrier, invalidation, freshness and rejection proofs establish the substantive facts separately.

The following names are in `NewLang.F0.Counterexample.Store`:

| Theorem | Concrete witness or break-test |
| --- | --- |
| `before_wellFormed` | Every fixture dependency/discardability combination starts well formed |
| `store_can_eliminate_old_only_dependency` | Old self-dependency and a concrete legal store |
| `old_self_dependency_rejects_replace_but_allows_store` | Same pre-state/incoming/fresh fact rejects all comparable replaces and admits store |
| `old_only_dependency_removed_from_validation` | Old dependent record retained, carrier gone, post dependencies valid |
| `incoming_need_not_be_discardable` | Legal store installs a non-discardable incoming value |
| `other_survivor_dependency_is_rejected` | Third loose survivor carrying old dependency rejects every candidate legal store |
| `incoming_dependency_is_rejected` | Dependent incoming package rejects every candidate legal store |
| `nondiscardable_old_package_is_rejected` | Non-discardable fixture rejects every raw candidate |
| `unchecked_other_dependency_breaks_candidate` | Raw candidate satisfies all other invariant fields but fails dependency validity |
| `unchecked_discardability_silently_loses_package` | Omitting just the discardability premise loses a non-discardable old carrier despite well-formed pre/post states |
| `currently_dead_fact_cannot_be_reused` | Recorded retired identity is dead but rejected for allocation |

The fixture has one live root, loose incoming and third packages, and a retained dead identity. The old package depends on its own current fact; the positive example's other packages have no dependencies. The old value is discardable while the incoming value is non-discardable. The same old-current dependency is valid initially and invalidated by either operation; carrier survival alone explains their difference.

Broken premise lists and countermodels stay in the isolated counterexample module. No unchecked store relation is added to the production kernel. Discardability remains a transition precondition rather than an artificial WellFormed field.

## Verification and PR workflow

Required local commands:

```bash
lake build
bash scripts/check-proofs.sh
```

The checker builds all project modules, scans project-owned Lean for proof placeholders/custom axiom declarations, and audits **57 theorem reports**: the existing 23 plus all 34 new public store/helper/fixture theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No custom semantic assumptions are introduced.

The unchanged `Lean proofs` workflow runs on push and pull_request, bootstraps pinned tools in empty temporary paths, and runs the same proof audit with the committed manifest. Development uses branch `f0.2-store`, an open PR targeting `main`, and confirmation of the pull_request-event run. CI results are recorded on the PR; CI success does not authorize merging it.

## Findings and next milestone

- **FORMAL-ENCODING:** Atomic carrier consumption, inactive retained table records, and existing Boolean static discardability are non-normative proof choices.
- **FORMAL-LEMMA:** Survivor preservation plus old-fact invalidation separates old-only acceptance from incoming/third-survivor rejection. The same-state replace/store witness rules out vacuous legality.
- **FORMAL-SCOPE:** Only store was added; all F0.1 proofs remain valid. No swap, lifetime operation, ptr/ref, aggregate/sum, general transition framework, or incarnation-history allocation was added.
- No new **FORMAL-HOLE**, **FORMAL-AMBIGUITY**, or **FORMAL-EXTRACTION** issue was found. The resolved milestone-number correction remains in the formalization notes.

After semantic/formalization review and merge, the foundation is ready for F0.3 — swap. Whole-language type safety and compiler correctness remain outside the established claims.
