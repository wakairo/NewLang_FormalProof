# NewLang F0 Formal Kernel — F0.6

[日本語](README.ja.md)

F0.0–F0.5 are reviewed and merged. F0.6 separates LifetimeDomain identity from its abstract value carrier: transfer moves the carrier while keeping the same live DomainId, governed roots and dependencies; explicit finalization ends the identity and consumes its carrier entry. Governed roots and surviving DomainLive dependencies permit transfer but block finalization. F0.6 is implemented; PR review and F0 closure review are pending.

## Specification boundary

1. [NewLang v0 Draft 17.4](docs/NewLang_v0_spec_Draft17_4.md) is the normative specification and source of truth.
2. [F0 Formal Kernel Specification Draft 0](docs/F0_Formal_Kernel_Specification.md) is a non-normative bridge.
3. The Lean model is an encoding for theorem proving.

**Formal representation choices are non-normative.**

The six core nominal ID types and the additional abstract `DomainValueCarrierId` wrap natural numbers. Finsets, function-based maps, package IDs, and Boolean discardability do not prescribe NewLang compiler or runtime representations. A domain value carrier is not a machine address, PlaceId, RootLocationId, PackageId or incarnation. Proof convenience must not change the normative semantics. Draft 17.4 is preserved verbatim. The non-normative F0 bridge retains its original Japanese text, with implementation traceability notes and the milestone-number correction recorded as resolved FORMAL-EXTRACTION history.

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
| `NewLang/F0/Id.lean` | Six core nominal identities (F0 §4) and an abstract domain value carrier identity |
| `NewLang/F0/Fact.lean` | Value facts and domain liveness; F0 §5 |
| `NewLang/F0/Package.lean` | Finite dependencies and discardability; F0 §6 |
| `NewLang/F0/State.lean` | Vacant/live occupancy, packages, loose packages, live domains, allocation histories and domain carrier map; F0 §7–9 / §20 |
| `LiveFacts` | Derived from occupancy and live domains; F0 §5, Draft 17.4 §13.5a |
| `CarrierUnique` | No duplicate installation or installed/loose overlap; F0 WF-1 |
| `PlacesUnique` | One live root and current fact per place; F0 WF-4 |
| `IncarnationsUnique` | One live root per incarnation; Draft 17.4 §3.5 |
| `PackagesPresent` | Every surviving carrier references a defined package; F0 WF-7 |
| `DomainsValid` | A live root's governing domain is live; F0 WF-5, Draft 17.4 §13.2 |
| `DependenciesValid` | Every surviving dependency is live; F0 WF-6, Draft 17.4 §13.5a |
| `ValueFactsRecorded` | Every current fact belongs to the proof-only allocation history |
| `IncarnationsRecorded`, `LiveIncarnation` | Recorded live incarnations and a derived liveness view |
| `DomainCarrierCoherent` | A domain is live iff its current value carrier exists; no reverse carrier injectivity |
| `NewLang/F0/Replace.lean` | Atomic candidate, raw relation, legal step, and replace-specific proofs |
| `NewLang/F0/Counterexample/Replace.lean` | Isolated positive examples and dependency/freshness countermodels |
| `NewLang/F0/Store.lean` | Atomic store candidate, discardability premise, raw/legal relations and proofs; F0 §15, Draft 17.4 §13.5a / §17.4 |
| `NewLang/F0/Counterexample/Store.lean` | Same-state replace/store contrast, legal store witness, survivor and discardability break-tests |
| `NewLang/F0/Swap.lean` | Same/distinct raw relations, atomic candidate, fresh pair, legal step and swap proofs; F0 §16, Draft 17.4 §13.5a / §17.4 |
| `NewLang/F0/Counterexample/Swap.lean` | Legal same/distinct witnesses, self/cross/cyclic/third rejection and freshness break-tests |
| `NewLang/F0/Lifetime.lean` | Fixed site/place layout, initialize/take/destroy raw/legal relations, governing relation lifecycle; Draft 17.4 §14 / F0 §17–19 |
| `NewLang/F0/Counterexample/Lifetime.lean` | Lifetime legal witnesses, survivor contrast, occupancy round-trip, fresh reinitialization and omitted-check tests |
| `NewLang/F0/Reference.lean`, `Counterexample/Reference.lean` | Persistent ptr / point-of-acquisition legality and stale-token controls; F0.5 |
| `NewLang/F0/Domain.lean` | Domain transfer/finalization candidates, raw/legal relations and no-stranding proofs; Draft 17.4 §13.1–3 / §14.5–6 |
| `NewLang/F0/Counterexample/Domain.lean` | Transfer/end contrasts, legal lifecycle/acquisition witnesses and three isolated break-tests |

WF-2/3/8 follow structurally from exclusive occupancy and its derived installed carrier. Carriers distinguish locations, and `PlacesUnique` establishes their correspondence with live places. Malformed roots sharing a place cannot hide duplicate package installation.

Occupancy is a total function; the package table is an Option-valued partial map. A table record without a carrier is not a survivor. Both installed and loose carriers must reference existing packages. `LiveFacts` includes only facts derived from current occupancy and domains, not independently retained historical facts.

## Historical freshness (proof-only ghost state)

`State.usedValueFacts : Finset ValueFactId` records all identities allocated in the modeled execution history, including retired facts. `FreshValueFact s vf` means `vf ∉ s.usedValueFacts`; `ValueFactsRecorded` requires every live current fact to be recorded. `State.empty` has empty history, and the original F0.0 smoke theorems are reproved.

Each raw replace or store inserts its new identity; distinct swap inserts two mutually distinct fresh identities. Same-place swap allocates nothing. All retain the whole previous history. `replace_history_monotone` / `store_history_monotone` and their old-fact retention theorems prove this retention. Thus an allocated identity cannot become eligible for reuse merely by becoming dead. A concrete countermodel has identity 2 recorded but currently dead and proves it cannot be fresh. Initial states must seed the history with all earlier allocations; future allocating transitions must preserve and extend it, never reconstruct it from live facts.

This history is **proof-only ghost state**, not a normative requirement for compiler/runtime history storage. F0.4 implements `usedIncarnations : Finset IncarnationId`, `FreshIncarnation` and `IncarnationsRecorded` using the same pattern. All existing candidates preserve incarnation history exactly, and their fixtures seed every live incarnation. Initialize extends both histories; take/destroy preserve both without erasing ended IDs. This is a proof encoding extension, not a revision of F0.1–F0.3 semantics. Payload, authority algebra, finite-support proofs, borrow checking, structural places, scope/backing facts, and other operations remain outside this milestone.

## Replace semantics

`replaceCandidate` changes exactly the selected location's current fact and package. Place, incarnation, governing domain, location, and live-root status are retained; all other locations, package data, and live domains are unchanged. It removes the incoming package from loose carriers, inserts the old package as the loose result, and extends the used-fact history.

`RawReplace canWrite typeCompatible s location root incoming newFact s'` witnesses the pre-state live root, incoming loose package, historical freshness, two caller-supplied static obligations, and equality with that candidate. The result package is `root.package`. The obligations are proposition parameters requiring proofs; production semantics do not fix them to True. Fixtures use True only to isolate the state/dependency rules. No exclusive reference or lifetime-ending authority is required.

`ReplaceStep` requires a well-formed pre-state, this raw relation, and a well-formed candidate post-state. The preservation theorem is intentionally a projection of the post-state condition, not a claim that every raw replace is legal. The substantive evidence is separate: explicit candidate updates, carrier transfer, historical freshness, old-fact invalidation, and rejection proofs for surviving dependencies. The dependency-free fixture also proves that a legal replace exists.

## Store semantics

At the visible value level, store behaves like replacement whose old value is discarded. **For dependency legality, store is one combined transition. It is not defined as “first require a legal ReplaceStep, then discard its result.”**

`storeCandidate` updates the same location's current fact and installed package, removes the incoming and old packages from loose carriers, retains package-table data and live domains, and extends historical freshness. `RawStore` records the same caller write/type premises as replace, plus an existing old `ValuePackage` with `discardable = true`. It does not require the incoming package to be discardable, an exclusive reference, or lifetime-ending authority. There are no destructor/Drop semantics.

`StoreStep = WellFormed pre ∧ RawStore ∧ WellFormed post`. The unit result carries no old package. Pre-state carrier uniqueness excludes incoming = old and any second old installation. Therefore the old package has **no surviving carrier**, even though its table record remains. Dependencies are checked only for post-state survivors; uncarried records are inactive data in this proof encoding, not a runtime memory-management claim.

The preservation theorem projects post-state legality; substantive lemmas separately prove the update, old-carrier consumption, old-fact invalidation, frame, and history retention. The same concrete pre-state with a discardable self-dependent old value admits store and rejects every comparable replace. A third loose survivor or incoming value carrying that dependency rejects store. Removing the discardability guard can lose a non-discardable package despite a well-formed post-state, demonstrating that the guard belongs to transition legality.

## Swap semantics

`SwapCase.same location root` has no fresh-fact arguments. `RawSwapSame` requires a live target and caller write/type premises, with `post = pre`. Thus history, current fact, package, incarnation, domain and every other field are unchanged; a self-dependent package remains legal.

`SwapCase.distinct` carries two live roots/locations and two new facts. `RawSwapDistinct` requires distinct locations, write authorization for both operands, type agreement, and `FreshValueFactPair s a b = FreshValueFact s a ∧ FreshValueFact s b ∧ a ≠ b`. WellFormed place uniqueness establishes distinct places, and carrier uniqueness derives distinct installed packages rather than adding that raw premise.

`swapCandidate` is one atomic exchange. Each location retains its place, incarnation and governing domain; package IDs exchange, both current facts freshen, and history records both without forgetting old allocations. Other occupancy, package/dependency data, loose carriers and live domains are unchanged. There is no intermediate replace/take/initialize state, dependency retargeting, or discarded value.

`RawSwap` dispatches only these two swap cases; `SwapStep` checks WellFormed pre/raw/post. `SwapSameStep` / `SwapDistinctStep` are case-specific abbreviations. Production caller premises remain abstract; True appears only in isolated fixtures. **F0.3 does not introduce a Copy requirement.** It also requires no Discardable, exclusive reference or lifetime-ending authority. A legal distinct witness has both package discardability flags false and different governing domains.

Both old packages survive at the opposite locations, while both old facts die. The ordinary post-state `DependenciesValid` rejects left/right self and cross dependencies, cyclic laundering, and dependencies in any third survivor. Packages move; exact dependencies never retarget. The same self-dependent pre-state permits same-place swap and rejects distinct swap. A cyclic raw candidate satisfies every other WellFormed field and fails only dependency validity.

## Lifetime / occupancy semantics

F0.4 abstracts source-level slot/ptr/ref and backing geometry using a root location, Vacant/live occupancy, package carriers and domains. **Root-only requirement is structurally satisfied by F0 scope:** every live occupancy is a lifetime root. Vacant represents the site's empty occupancy responsibility; no explicit slot value, PtrToken, subobject, Storage or BackingRegion is introduced.

`RootSiteLayout` is an immutable, injective `RootLocationId → PlaceId` association fixed in the proof context of an execution. Initialize obtains the place from that same layout/site, without minting a fresh PlaceId. Nominal types remain distinct, and older states gain no new global layout-coherence invariant. Existing operations preserve their root places. The lifecycle witness uses the same layout/location for both starts and proves identical places with different incarnations. This is non-normative FORMAL-ENCODING; the numeric layout used by fixtures is not a runtime format.

`RawInitialize` requires a vacant target, loose incoming package, supplied live domain, fresh incarnation/current fact, ordinary initialization authorization and type agreement. It installs the incoming package, creates a governing relation to the **supplied domain**, and inserts both identities into ghost history. It requires neither Discardable nor lifetime-ending authority. The incoming package table is unchanged; governing state is not recovered from its dependencies or value data.

`RawTake` / `RawDestroy` require a live root, `endingDomain = root.governing` and a caller proof of `CanEndRoot` (an abstract Prop, never universally True in production). Both end the incarnation/current fact/root governing relation and restore Vacant. **Domain identity itself stays live**, all other locations/package data are unchanged, and histories are retained. Take returns the old package as a loose survivor and permits non-discardable values. Destroy additionally requires the existing old-package discardability abstraction and consumes every old carrier; an inactive table record may remain.

At the visible value level destroy resembles take followed by discarding the returned value. Dependency legality checks one combined destroy candidate; it does not first require a legal TakeStep. Thus old-only self-dependency rejects take but can be consumed by destroy, while a third surviving dependent package rejects both. `destroy uses the existing proof-side abstraction; this is not a runtime package flag requirement.` No destructor/Drop semantics is added.

`InitializeStep`, `TakeStep`, `DestroyStep` all check WellFormed pre/raw/post. Preservation projections are supplemented by explicit carrier/history/frame, identity end and negative dependency proofs. The concrete initialize/take/reinitialize witness restores a unique loose package carrier and the same vacancy; history prevents equality with the original state and prevents old incarnation reuse. Governs/LiveIncarnation are derived views, not separate mutable relation tables.

## F0.5 ptr / ref acquisition

`PtrToken` has exactly `location : RootLocationId` and `incarnation : IncarnationId`. It is a persistent external mathematical value; no token registry is added to State. It contains neither current ValueFactId nor DomainId. Arbitrary Lean construction is not source-safe issuance, and Lean equality is not source-level pointer equality. `initialize_yields_current_ptr` connects a successful existing InitializeStep to its corresponding result token; no pre-lifetime minting operation is introduced.

`RawAcquireRef stable access s ptr evidenceDomain` requires a live root at the exact location, identical incarnation, matching governing DomainId, a proof of `stable` and a proof of `access`. `AcquireRef` also requires WellFormed s. Acquisition is a Prop derivation, with no state mutation and no persistent RefToken. The evidence domain is separate from possession of ordinary stability evidence; even a live domain does not establish that possession. `access` abstracts provenance, representation, originating BackingRegion liveness, alignment, range and required read/write access. Production never fixes either caller proposition to True. This is the common acquisition kernel, with no exclusive/write-equals-ending-authority requirement.

AcquireRef proves point-of-acquisition legality/current liveness. It does not yet prove full future-use scope stability. No lexical scope graph, ref non-escape, general read/write semantics, or ref-to-ptr conversion is introduced.

The same fixed RootSiteLayout and location are used in both take/reinitialize and destroy/reinitialize fixtures. In the final live state, old ptr fails and freshly issued ptr succeeds. Replace changes the current value fact while the same ptr remains usable. Three private break-tests isolate omitted incarnation freshness, omitted acquisition incarnation match, and omitted domain match; the freshness-only example satisfies all other raw initialize conditions and all pre/post WellFormed fields.

The [F0.5 report](docs/F0_5_PTR_REF_ACQUISITION_REPORT.md) lists its 28 added audits (18 production, 10 concrete controls/countermodels), preserving the prior 180. During F0.5, State and WellFormed were unchanged. F0.6 now extends them as described below; existing public theorem statements, toolchain pins and normative Draft 17.4 remain unchanged.

## F0.6 domain transfer / finalization

`State.domainValueCarrier : DomainId → Option DomainValueCarrierId` tracks abstract ownership independently of root/package carriers. `DomainCarrierCoherent s` requires `D ∈ s.liveDomains ↔ ∃ c, s.domainValueCarrier D = some c`. Option gives one current carrier per domain; several domains may share one carrier. This proof encoding does not model the place/incarnation of an actual LifetimeDomain-typed object. Empty state has no carriers; older fixtures seed live domains and all earlier operation candidates preserve the map exactly.

`domainTransferCandidate s D newCarrier` changes only D's carrier entry. `RawDomainTransfer transferAllowed s D oldCarrier newCarrier post` requires D live, the matching old carrier, a caller proof of `transferAllowed`, and candidate equality. That premise abstracts unmodeled source-current-value capability conflicts and ordinary transfer applicability. It is never universally True in production. Governed roots and DomainLive-dependent survivors are not transfer blockers: identity, live domains, occupancy/Governs, package/dependency data, loose carriers, LiveFacts and both histories are unchanged. A raw transfer from a well-formed state preserves WellFormed, and `DomainTransferStep` explicitly records pre/raw/post legality.

`finalizeDomainCandidate s D` removes D from liveDomains and clears only its carrier entry. `RawFinalizeDomain canFinalize s D carrier post` requires a live domain, matching carrier, a caller proof for omitted scoped-capability/applicability conditions, and candidate equality. `FinalizeDomainStep` also checks WellFormed pre/post. Roots, packages, dependencies and histories are unchanged; there is no automatic root destruction or retargeting. Post-state DomainsValid derives the no-governed-root condition, and DependenciesValid derives the no-surviving-DomainLive-dependency condition. These modeled conditions are not duplicated as raw guards. Finalization consumes D's ownership entry, not every domain sharing that carrier.

Concrete controls prove transfer remains legal with a governed root or domain-dependent survivor while finalization rejects, legal independent finalization exists, and destroy can end a root before later finalization. Transfer preserves acquisition for the same ptr and DomainId **given post-state caller stability/access proofs**; this does not prove an acquired ref remains usable through arbitrary future scopes. Dead domains, wrong carriers and missing caller permission reject. A private identity-renaming transfer has well-formed endpoints but violates the real transfer relation. Two unchecked finalization candidates fail only DomainsValid or only DependenciesValid, respectively, while the other eight fields hold.

LifetimeDomain's non-Discardable boundary is represented by explicit finalization, separate from `ValuePackage.discardable`; no implicit domain-discard operation exists. F0.6 adds no domain creation, usedDomainIds, general authority algebra or F1 geometry. Fresh domain creation/recreation remains a future obligation under Draft 17.4 §13.1. See the [F0.6 report](docs/F0_6_DOMAIN_TRANSFER_FINALIZATION_REPORT.md) for all 58 added audits, M8 feedback and the limited F0 closure assessment.

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

F0.3 adds 45 audited production/helper/fixture theorems: same-case identity/history/current/package and legality; distinct preservation, exchange and survival; pair freshness/history; both old-fact invalidation lemmas; generic and left/right self/cross rejection; reused/colliding fact rejection; independent and non-discardable witnesses; same-vs-distinct contrast; cyclic/third-survivor rejection and the broken dependency-check countermodel. See the [complete F0.3 theorem inventory](docs/F0_3_SWAP_REPORT.md). All existing F0.0/F0.1/F0.2 proofs remain checked.

F0.4 audits 78 additional declarations: four incarnation-history preservation lemmas for prior operations, 54 lifetime production/helper theorems and 20 concrete fixtures. The [complete F0.4 inventory/report](docs/F0_4_LIFETIME_OCCUPANCY_REPORT.md) covers initialization, vacancy/carrier conservation, fresh reinitialization, take/destroy survivor contrast, governing relation end versus domain survival, authorization/domain/discardability rejection and three omitted-check tests. Existing theorem statements and semantic claims remain unchanged; all 102 earlier audits still pass with correctly seeded ghost state.

`lake build` checks both production and isolated validation modules. `scripts/check-proofs.sh` scans project-owned Lean sources for `sorry` / `axiom` / `admit`, then checks 266 theorem axiom reports against only `propext`, `Classical.choice`, and `Quot.sound`. All previous 208 audits remain. It preserves Lean failures and handles multiline reports. Specification prose and mathlib sources are outside the project-source scan.

## GitHub Actions

[`.github/workflows/lean.yml`](.github/workflows/lean.yml) runs on push and pull_request with read-only repository permissions, Ubuntu 24.04, and checkout pinned to its v6.1.0 commit. It installs bootstrap prerequisites, uses empty runner-temporary toolchain/cache paths, and executes `scripts/bootstrap.sh`, which runs `lake build` and the proof checker using the committed Lean pin and dependency manifest. It never selects latest Lean or updates the manifest. No additional CI service or secret is required. Development uses a dedicated branch and an open PR targeting `main`; the pull_request-triggered Lean proofs run must pass before semantic review. CI success does not merge the PR.

## Milestones and next step

| Milestone | Scope |
| --- | --- |
| F0.0 | State / WellFormed — complete |
| F0.1 | replace — complete |
| F0.2 | store — complete |
| F0.3 | swap — complete |
| F0.4 | initialize / take / destroy — reviewed and merged |
| F0.5 | ptr / ref acquisition — reviewed and merged |
| F0.6 | LifetimeDomain transfer / finalization — implemented; PR review pending |

After F0.6 semantic review, the next step is **F0 closure review**, followed by a separately decided F1 scope. Ref scope/non-escape, backing geometry and structural subobjects remain unimplemented. The checked flat kernel does not establish whole-language memory/type safety or compiler correctness. This milestone stops before F1 implementation.

See [formalization notes](docs/FORMALIZATION_NOTES.md) ([日本語](docs/FORMALIZATION_NOTES.ja.md)) and milestone reports: [F0.1](docs/F0_1_REPLACE_REPORT.md), [F0.2](docs/F0_2_STORE_REPORT.md), [F0.3](docs/F0_3_SWAP_REPORT.md), [F0.4](docs/F0_4_LIFETIME_OCCUPANCY_REPORT.md), [F0.5](docs/F0_5_PTR_REF_ACQUISITION_REPORT.md), [F0.6](docs/F0_6_DOMAIN_TRANSFER_FINALIZATION_REPORT.md).
