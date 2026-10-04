# NewLang F0 Formal Kernel — F0.2

[日本語](README.ja.md)

F0.0 established the flat state and well-formedness model; F0.1 added historical freshness and `replace`. F0.2 adds atomic `store`: a discardable old package can carry an old-current dependency without blocking its own consumption, while dependencies in surviving packages still reject the operation. A concrete proof compares illegal replace and legal store from the same pre-state. Only `replace` and `store` are implemented.

## Specification boundary

1. [NewLang v0 Draft 17.4](docs/NewLang_v0_spec_Draft17_4.md) is the normative specification and source of truth.
2. [F0 Formal Kernel Specification Draft 0](docs/F0_Formal_Kernel_Specification.md) is a non-normative bridge.
3. The Lean model is an encoding for theorem proving.

**Formal representation choices are non-normative.**

The six nominal ID types wrap natural numbers. Finsets, function-based maps, package IDs, and Boolean discardability do not prescribe NewLang compiler or runtime representations. Proof convenience must not change the normative semantics. Draft 17.4 is preserved verbatim. The non-normative F0 bridge retains its original Japanese text, with the milestone-number correction recorded as resolved FORMAL-EXTRACTION history.

## Pinned environment

| Component | Pin |
| --- | --- |
| Lean / Lake | `leanprover/lean4:v4.34.1` in `lean-toolchain` |
| Lean release commit | `5045d0056413266e57c625dcd7c365b10e377c52` |
| elan | `4.2.4` in the cloud bootstrap |
| mathlib | `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| All transitive dependencies | Full Git revisions in `lake-manifest.json` |

At setup on 2026-10-04, v4.34.1 was the latest stable release of both Lean and mathlib. Mathlib's own toolchain pin matches this Lean version. The mathlib revision is fixed in both `lakefile.toml` and the manifest.

## Reproduce on Codex Cloud

Use the existing checkout at `/workspace/NewLang_FormalProof`, which is the conceptual `newlang-formal/` root. Cloud tasks are already isolated; do not create another worktree unless explicitly requested.

Base prerequisites: Bash, Git, curl, tar, zstd, sha256sum, and ripgrep. Preinstalled Lean or mathlib is not required.

```bash
cd /workspace/NewLang_FormalProof
bash scripts/bootstrap.sh
export ELAN_HOME=/workspace/.local/elan
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR=/workspace/.cache/mathlib
lean --version
lake build
bash scripts/check-proofs.sh
```

The x86_64 Linux bootstrap downloads fixed official GitHub release archives, verifies their pinned SHA-256 digests, and registers Lean under the repository's toolchain name with `elan toolchain link`. Digests come from the official release asset metadata. TLS verification remains enabled. This route works without elan's release-discovery endpoint.

The script resolves the existing manifest without `lake update`, fetches the cache for the imported mathlib modules, and builds the project. The initial import closure contains 591 modules. A source build with `lake build` is also possible if the cache is unavailable, but takes longer. After adding imports, fetch their closure with `lake exe cache get Module.Name`.

For deliberate upgrades, update the Lean pin, mathlib revision, bootstrap checksums, and manifest together and validate the result. Routine setup must not update the lockfile.

Network access uses GitHub/the Git proxy, `release-assets.githubusercontent.com`, `cache.mathlib.org`, and `lakecache.blob.core.windows.net`. Native elan 4.2.4 release discovery also uses `release.lean-lang.org`. Keep the environment's existing package-manager network preset. No application credentials or running services are required.

To retain the prepared cloud filesystem for future tasks, review/save the environment configuration and Publish it. A fresh Git checkout can instead reproduce the environment using the repository bootstrap and manifest.

## Other development environments

With elan installed for your platform, run these commands from the repository root:

```bash
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Data.Set.Basic
lake build
bash scripts/check-proofs.sh
```

The cloud bootstrap can also run on other x86_64 Linux machines with writable paths:

```bash
ELAN_HOME="$HOME/.elan" \
NEWLANG_TOOLCHAIN_ROOT="$HOME/.local/share/newlang-lean" \
MATHLIB_CACHE_DIR="$HOME/.cache/mathlib" \
bash scripts/bootstrap.sh
```

The cloud bootstrap was tested from empty toolchain directories and a project copy containing no dependencies or build outputs. The native elan instructions are an alternative for other platforms.

## Model and traceability

| File / definition | Scope and source |
| --- | --- |
| `NewLang/F0/Id.lean` | Six nominally distinct identities; F0 §4 |
| `NewLang/F0/Fact.lean` | Value facts and domain liveness; F0 §5 |
| `NewLang/F0/Package.lean` | Finite dependencies and discardability; F0 §6 |
| `NewLang/F0/State.lean` | Vacant/live occupancy, packages, loose packages, live domains; F0 §7–9 |
| `LiveFacts` | Derived from occupancy and live domains; F0 §5, Draft 17.4 §13.5a |
| `CarrierUnique` | No duplicate installation or installed/loose overlap; F0 WF-1 |
| `PlacesUnique` | One live root and current fact per place; F0 WF-4 |
| `IncarnationsUnique` | One live root per incarnation; Draft 17.4 §3.5 |
| `PackagesPresent` | Every surviving carrier references a defined package; F0 WF-7 |
| `DomainsValid` | A live root's governing domain is live; F0 WF-5, Draft 17.4 §13.2 |
| `DependenciesValid` | Every surviving dependency is live; F0 WF-6, Draft 17.4 §13.5a |
| `ValueFactsRecorded` | Every current fact belongs to the proof-only allocation history |
| `NewLang/F0/Replace.lean` | Atomic candidate, raw relation, legal step, and replace-specific proofs |
| `NewLang/F0/Counterexample/Replace.lean` | Isolated positive examples and dependency/freshness countermodels |
| `NewLang/F0/Store.lean` | Atomic store candidate, discardability premise, raw/legal relations and proofs; F0 §15, Draft 17.4 §13.5a / §17.4 |
| `NewLang/F0/Counterexample/Store.lean` | Same-state replace/store contrast, legal store witness, survivor and discardability break-tests |

WF-2/3/8 follow structurally from exclusive occupancy and its derived installed carrier. Carriers distinguish locations, and `PlacesUnique` establishes their correspondence with live places. Malformed roots sharing a place cannot hide duplicate package installation.

Occupancy is a total function; the package table is an Option-valued partial map. A table record without a carrier is not a survivor. Both installed and loose carriers must reference existing packages. `LiveFacts` includes only facts derived from current occupancy and domains, not independently retained historical facts.

## Historical freshness (proof-only ghost state)

`State.usedValueFacts : Finset ValueFactId` records all identities allocated in the modeled execution history, including retired facts. `FreshValueFact s vf` means `vf ∉ s.usedValueFacts`; `ValueFactsRecorded` requires every live current fact to be recorded. `State.empty` has empty history, and the original F0.0 smoke theorems are reproved.

Each raw replace or store inserts its new identity and retains the whole previous history. `replace_history_monotone` / `store_history_monotone` and their old-fact retention theorems prove this retention. Thus an allocated identity cannot become eligible for reuse merely by becoming dead. A concrete countermodel has identity 2 recorded but currently dead and proves it cannot be fresh. Initial states must seed the history with all earlier allocations; future allocating transitions must preserve and extend it, never reconstruct it from live facts.

This history is **proof-only ghost state**, not a normative requirement for compiler/runtime history storage. A separate `usedIncarnations : Finset IncarnationId` can follow the same pattern for F0.4; it is not implemented yet. Payload, authority algebra, finite-support proofs, borrow checking, structural places, scope/backing facts, and other operations remain outside this milestone.

## Replace semantics

`replaceCandidate` changes exactly the selected location's current fact and package. Place, incarnation, governing domain, location, and live-root status are retained; all other locations, package data, and live domains are unchanged. It removes the incoming package from loose carriers, inserts the old package as the loose result, and extends the used-fact history.

`RawReplace canWrite typeCompatible s location root incoming newFact s'` witnesses the pre-state live root, incoming loose package, historical freshness, two caller-supplied static obligations, and equality with that candidate. The result package is `root.package`. The obligations are proposition parameters requiring proofs; production semantics do not fix them to True. Fixtures use True only to isolate the state/dependency rules. No exclusive reference or lifetime-ending authority is required.

`ReplaceStep` requires a well-formed pre-state, this raw relation, and a well-formed candidate post-state. The preservation theorem is intentionally a projection of the post-state condition, not a claim that every raw replace is legal. The substantive evidence is separate: explicit candidate updates, carrier transfer, historical freshness, old-fact invalidation, and rejection proofs for surviving dependencies. The dependency-free fixture also proves that a legal replace exists.

## Store semantics

At the visible value level, store behaves like replacement whose old value is discarded. **For dependency legality, store is one combined transition. It is not defined as “first require a legal ReplaceStep, then discard its result.”**

`storeCandidate` updates the same location's current fact and installed package, removes the incoming and old packages from loose carriers, retains package-table data and live domains, and extends historical freshness. `RawStore` records the same caller write/type premises as replace, plus an existing old `ValuePackage` with `discardable = true`. It does not require the incoming package to be discardable, an exclusive reference, or lifetime-ending authority. There are no destructor/Drop semantics.

`StoreStep = WellFormed pre ∧ RawStore ∧ WellFormed post`. The unit result carries no old package. Pre-state carrier uniqueness excludes incoming = old and any second old installation. Therefore the old package has **no surviving carrier**, even though its table record remains. Dependencies are checked only for post-state survivors; uncarried records are inactive data in this proof encoding, not a runtime memory-management claim.

The preservation theorem projects post-state legality; substantive lemmas separately prove the update, old-carrier consumption, old-fact invalidation, frame, and history retention. The same concrete pre-state with a discardable self-dependent old value admits store and rejects every comparable replace. A third loose survivor or incoming value carrying that dependency rejects store. Removing the discardability guard can lose a non-discardable package despite a well-formed post-state, demonstrating that the guard belongs to transition legality.

## Machine-checked theorem inventory

All names below are in `NewLang.F0` unless qualified otherwise.

| Theorem | Checked property |
| --- | --- |
| `wellFormed_surviving_dependencies_live`, `empty_wellFormed` | Retained F0.0 smoke proofs |
| `replace_preserves_wellFormed` | Legal replace preserves the invariant |
| `replace_preserves_incarnation`, `replace_preserves_governingDomain` | Lifetime state is retained |
| `replace_preserves_place_and_location`, `replace_preserves_other_locations` | Target identity/status and frame |
| `replace_preserves_package_data_and_domains` | Package dependencies and domain set are unchanged |
| `replace_creates_fresh_current_fact` | New fact was not used before, is current, and is now recorded |
| `replace_history_monotone`, `replace_old_fact_remains_used` | No allocation history is forgotten |
| `replace_old_package_survives_as_loose` | Old value survives as the loose result |
| `replace_new_package_installed` | Incoming package is installed and no longer loose |
| `rawReplace_old_current_fact_not_live` | Target's old current fact is dead after raw replace |
| `replace_rejects_surviving_old_current_dependency` | Old-package dependency cannot escape through the result |
| `replace_rejects_incoming_old_current_dependency` | Incoming dependency on the invalidated fact also rejects |
| `replace_rejects_previously_used_fact` | Historical reuse rejects even for retired identities |

`NewLang.F0.Counterexample.Replace` contains `before_wellFormed`, `independent_replace_is_legal`, `unchecked_replace_launders_old_dependency`, `old_dependency_is_rejected`, `incoming_dependency_is_rejected`, and `currently_dead_is_not_historically_fresh`. The malformed raw candidate satisfies every other WellFormed field and fails specifically `DependenciesValid`; a separate broken production Step is not introduced.

F0.2 additionally checks `store_preserves_wellFormed`, `store_preserves_incarnation`, `store_preserves_governingDomain`, `store_preserves_place_and_location`, `store_preserves_other_locations`, `store_preserves_package_data_and_domains`, `store_creates_fresh_current_fact`, `store_history_monotone`, `store_old_fact_remains_used`, `store_new_package_installed`, `store_old_package_does_not_survive`, `rawStore_old_current_fact_not_live`, `store_other_survivors_preserved`, both surviving/incoming dependency rejection theorems, discardability rejection and historical-reuse rejection. The [F0.2 report](docs/F0_2_STORE_REPORT.md) lists every new audited theorem, including the concrete contrast and three break-tests. All existing F0.1 proofs remain checked.

`lake build` checks both production and isolated validation modules. `scripts/check-proofs.sh` scans project-owned Lean sources for `sorry` / `axiom` / `admit`, then checks 57 theorem axiom reports against only `propext`, `Classical.choice`, and `Quot.sound`. It preserves Lean failures and handles multiline reports. Specification prose and mathlib sources are outside the project-source scan.

## GitHub Actions

[`.github/workflows/lean.yml`](.github/workflows/lean.yml) runs on push and pull_request with read-only repository permissions, Ubuntu 24.04, and checkout pinned to its v6.1.0 commit. It installs bootstrap prerequisites, uses empty runner-temporary toolchain/cache paths, and executes `scripts/bootstrap.sh`, which runs `lake build` and the proof checker using the committed Lean pin and dependency manifest. It never selects latest Lean or updates the manifest. No additional CI service or secret is required. Development uses a dedicated branch and an open PR targeting `main`; the pull_request-triggered Lean proofs run must pass before semantic review. CI success does not merge the PR.

## Milestones and next step

| Milestone | Scope |
| --- | --- |
| F0.0 | State / WellFormed — complete |
| F0.1 | replace — complete |
| F0.2 | store — implemented; PR review pending |
| F0.3 | swap — next after F0.2 review |
| F0.4 | initialize / take / destroy |
| F0.5 | ptr / ref acquisition |
| F0.6 | LifetimeDomain transfer / finalization |

F0.3 can reuse the pinned environment, allocation history and candidate/dependency machinery after F0.2 review and merge. Swap and later operations are not implemented. Whole-language type safety and compiler correctness are not claimed.

See [formalization notes](docs/FORMALIZATION_NOTES.md) ([日本語](docs/FORMALIZATION_NOTES.ja.md)), the [F0.1 report](docs/F0_1_REPLACE_REPORT.md), and the [F0.2 report](docs/F0_2_STORE_REPORT.md).
