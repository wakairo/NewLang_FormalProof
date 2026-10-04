# F0.1 replace: proof evidence and boundary

## Changes

State and WellFormed now track historical value-fact allocation. `Replace.lean` implements only the replace candidate/relation/proofs. `Counterexample/Replace.lean` isolates positive examples and break-tests. `NewLang.lean` includes both modules in the build. The proof-check script audits the listed theorems and rejects nonstandard axioms. GitHub Actions reuses the pinned bootstrap. Both READMEs and formalization notes are updated, and the F0 bridge's domain-operation milestone is corrected to F0.6.

Lean 4.34.1, elan 4.2.4, mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, the complete dependency manifest, and the normative Draft 17.4 are unchanged.

## History

`usedValueFacts : Finset ValueFactId` is ghost allocation history; `FreshValueFact` means non-membership. `ValueFactsRecorded` ensures live current facts are in that history. A raw replacement inserts the chosen identity and preserves all prior members, including the old current identity. This makes reuse impossible along repeated replacements that carry this history forward. Initial states must include all earlier allocations. This is not a NewLang runtime representation requirement. A separate `usedIncarnations` can use the same design when lifetime operations enter scope.

## Transition

`RawReplace` takes the pre-state, target location and root witness, incoming package, chosen fresh fact, and post-state. The old root's package is the result. Caller-supplied write and type-compatibility propositions require proofs. No lifetime-ending authority is required.

The candidate updates the target's package/current fact, removes the incoming loose carrier, adds the old loose result, and extends history. It retains place/incarnation/domain/status/location, other locations, package data, and live domains. `ReplaceStep` additionally checks pre-state and candidate post-state WellFormedness.

## Proofs

The complete named inventory is in the [README](../README.md#machine-checked-theorem-inventory) and `scripts/check-proofs.sh` (23 audited reports, including the F0.0 smoke proofs and isolated validation theorems).

Preservation is a projection by design. It does not establish that every raw candidate is legal. The substantive non-laundering proof establishes:

1. Historical freshness and current-fact history coverage imply the new and old IDs differ.
2. The updated target no longer has its old fact; place uniqueness rules out another location keeping it live.
3. The old package survives as a loose result and retains its dependency data.
4. Post-state DependenciesValid would require that dead fact to be live, a contradiction.

`replace_rejects_surviving_old_current_dependency` therefore rules out every legal post-state for an old-current-dependent result. `replace_rejects_incoming_old_current_dependency` proves the corresponding incoming case.

## Concrete validation

| Input / omitted rule | Machine-checked outcome |
| --- | --- |
| No old or incoming dependency | A legal ReplaceStep exists |
| Old package depends on the old current fact | No legal ReplaceStep; the raw candidate fails only DependenciesValid |
| Incoming package depends on the old current fact | No legal ReplaceStep |
| ID 2 is recorded but currently dead | Not FreshValueFact; no RawReplace may allocate it |

Fixtures are in `NewLang.F0.Counterexample.Replace`, separate from production declarations. No broken legal Step is added. They use True static obligations only to isolate dependency/history behavior; the production relation remains parameterized.

`lake build` and `bash scripts/check-proofs.sh` check these proofs. Project-owned Lean sources contain no proof placeholders or added axioms. Audited theorem dependencies are limited to standard `propext`, `Classical.choice`, and `Quot.sound`.

## CI and remaining scope

`.github/workflows/lean.yml` runs the same pinned bootstrap/build/audit on push and pull_request from empty runner-temporary toolchain/cache paths. The workflow is statically checked with actionlint; the task's final report records the observed GitHub run separately.

The milestone correction is retained as resolved FORMAL-EXTRACTION history. Ghost history and carrier decisions are FORMAL-ENCODING; the non-laundering decomposition is FORMAL-LEMMA; excluded mechanisms remain FORMAL-SCOPE. No normative FORMAL-HOLE or FORMAL-AMBIGUITY was found in this scope.

The next milestone is F0.2 store. Its old package must not survive as a result. No store, swap, lifetime, domain, pointer, structural, scope, function-boundary, FFI, LLVM, or general effect operation is implemented here.
