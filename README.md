# NewLang F0 Formal Kernel — F0.0

[日本語](README.ja.md)

A minimal Lean 4 foundation for formalizing the NewLang v0 semantic kernel. F0.0 defines identities, facts, value packages, a flat state, derived live facts, and well-formedness. Operations and transition preservation are the next milestones.

## Specification boundary

1. [NewLang v0 Draft 17.4](docs/NewLang_v0_spec_Draft17_4.md) is the normative specification and source of truth.
2. [F0 Formal Kernel Specification Draft 0](docs/F0_Formal_Kernel_Specification.md) is a non-normative bridge.
3. The Lean model is an encoding for theorem proving.

**Formal representation choices are non-normative.**

The six nominal ID types wrap natural numbers. Finsets, function-based maps, package IDs, and Boolean discardability do not prescribe NewLang compiler or runtime representations. Proof convenience must not change the normative semantics. Both supplied specifications are preserved verbatim under their requested filenames, including their original Japanese text.

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

WF-2/3/8 follow structurally from exclusive occupancy and its derived installed carrier. Carriers distinguish locations, and `PlacesUnique` establishes their correspondence with live places. Malformed roots sharing a place cannot hide duplicate package installation.

Occupancy is a total function; the package table is an Option-valued partial map. A table record without a carrier is not a survivor. Both installed and loose carriers must reference existing packages. `LiveFacts` includes only facts derived from current occupancy and domains, not independently retained historical facts.

Payload, authority algebra, finite support, historical freshness, authorization, structural places, scope/backing facts, and transitions remain outside the verified F0.0 scope. Future transitions must state their freshness premises explicitly: currently unused does not imply historically fresh.

## Machine-checked smoke proofs

`wellFormed_surviving_dependencies_live` projects dependency liveness for surviving packages from `WellFormed`. `empty_wellFormed` proves that the empty state satisfies the invariant.

`lake build` checks the project sources and proofs. `scripts/check-proofs.sh` scans project Lean sources for proof placeholders or added axioms and prints the axioms of both theorems. Their only dependencies are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no semantic invariant is assumed through an added axiom. Specification prose and mathlib's sources are outside this project-source scan.

## Next milestone: F0.1 replace

Following F0 §28, add relational RawStep/Step definitions, a fresh current value fact, and transfer of the old package to a loose result. Include the negative lemma that an old package depending on the invalidated current fact prevents a legal replace step. No transition preservation or whole-language type safety is claimed yet.

See [formalization notes](docs/FORMALIZATION_NOTES.md) ([日本語](docs/FORMALIZATION_NOTES.ja.md)) for encoding decisions and the bridge document's milestone-number inconsistency.
