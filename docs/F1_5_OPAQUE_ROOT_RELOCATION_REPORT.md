# F1.5 — opaque lifetime-root relocation

Track: F

[Japanese primary report, full 77-declaration inventory and clause/control mapping](F1_5_OPAQUE_ROOT_RELOCATION_REPORT.ja.md).

Issue: [#16](https://github.com/wakairo/NewLang_FormalProof/issues/16). The Compiler development process was read first. Canonical authority is Compiler main `acac894fc6c50101a3995a8f930a070987529335`, `docs/reference/CURRENT_SPEC.md` selecting **Draft 17.9**, especially §24.4 with §3/§13.5a/§17.4/§24.3/§24.5. FormalProof main/base is `624df3bd4f1f69fc719a1382af44e8170a8ff9a5`. Both current mains matched the Issue's starting authority. Baseline build passed (720 jobs); all 757 baseline audits passed. Work uses `f1.5-opaque-root-relocation` and an open PR targeting main. Git is the change history; no parallel version ledger is introduced.

## Model and substantive results

`Relocation.State` wraps the actual existing F1.4 `Occupancy.SumState`. `WellFormed` explicitly retains its complete accounting, F1.2 shape/dependency invariants and backing/erasure obligations. Optional value-owned annotations expose existing persistent `F0.PtrToken` values and ledger claim handles. Surviving packages may reference only active value-owned claims, with no duplicate ownership between distinct survivors. An opaque extra-data marker is preserved; it does not implement or prove a general Allocation owner/capability system.

`Action.same` has no allocation parameters. Common source/destination/metadata identification and the existing live root claim give **exact state identity**, without ending/read/write/preparation guards. Consequently every incarnation/fact/occurrence/placement/history/token/accounting field is unchanged. A self-occurrence-dependent package remains legal even when ending and raw read/write privileges are false.

`Action.move` has a single `RawMove` candidate. It ends the source root and source placement, begins a fresh destination root/current facts/active occurrence, and installs the same package at the destination site exactly once. Destination domain identity remains D; its derived `(fresh incarnation,D)` relation key is fresh. Package/dependency/loose data and value-owned annotations do not change. The old persistent ptr remains representable but stale; a distinct fresh destination token is available. The currentness test agrees exactly with F0 erasure's `CurrentPtr`, and is not a complete safe dereference checker. No address-sensitive fixup occurs.

Freshness uses the existing historical `usedIncarnations`, `usedValueFacts`, `usedOccurrences` and `Conditional.FreshAllocation`. New IDs are recorded, all old history is retained, and ended identities cannot be reallocated merely because they are dead. Erasure gives explicit F1.4 → F1.3 → F1.2 → F1.1 → F0 well-formedness paths without separately assuming erased well-formedness.

The existing root-level sum slice erases to a singleton fixed-root layout. The sole retained fixed incarnation is proved fresh. Arbitrary fixed descendants, nested sums and general Allocation ownership are deliberately outside this bounded proof. Distinct moves use vacant destination sites and different nominal region/range extents. Static site/place correspondence is the existing F0.4 encoding; it is not a new global PlaceId allocator.

**Formal representation choices are non-normative.** Ghost histories/ledger, opaque annotations and the observation receipt are not runtime tags, ownership types or final source syntax. Identification/alignment/advance preparation are caller propositions, not a metadata/byte-copy implementation.

## Responsibility and dependency pressure tests

The actual F1.4 ledger consumes raw `D-S`, returns raw `S-D`, and never returns `S∩D` as duplicate raw responsibility. `RawMove.occupancy_conserved` proves whole-ledger footprint equality from the raw relation, **without post-state WF**. Legal steps use existing complete coverage and NoOverlap; every scoped byte has exactly one responsibility. Preservation itself is a legal-Step projection; the operation-specific identity, freshness, package frame, stale-token and footprint results are separate proofs.

Concrete legal endpoints cover:

- Same-region disjoint `S=[0,2)`, `D=[2,4)`.
- Partial overlap `S=[0,2)`, `D=[1,3)`: `S-D={byte0}`, intersection `{byte1}`, `D-S={byte2}`. A nested value-owned Storage `[3,4)` is retained.
- Distinct nominal region destination `[0,2)`.
- Exact same-place no-op with a self occurrence dependency and no ending/read/write privilege.

Old occurrence and exact payload facts become dead. Source and external surviving old-occurrence dependencies reject via the **same existing candidate-post `DependenciesValid`**, without erasing or retargeting dependencies. Address-sensitive embedded ptrs are transferred unchanged; no automatic self/interior/link/registry/callback fixup is claimed.

All fifteen required controls are machine checked and isolated in `Counterexample`: reused root/current/occurrence IDs; source placement transfer; copied governing key; retargeted old ptr receipt; package duplication/loss; raw intersection duplication; source-difference loss; destination-difference non-consumption; nominal region equality from a coincident hypothetical label; same-place end/restart; public half-state; embedded ptr fixup. Freshness controls reject the allocation premise for any endpoint. Placement/relation/ptr/fixup/half/loss controls have well-formed endpoint witnesses. The overlap duplicate/non-consumption controls retain accounting shape and exact union coverage but fail NoOverlap; the lost raw control retains shape and NoOverlap but fails coverage. They therefore obstruct the unchanged production Accounting guard. The primary report records the exact declaration for each control and does not claim every broken endpoint violates only one unrelated invariant.

## Findings and limits

- **FORMAL-ENCODING:** finite ghosts, exact extent differences, derived governing key, existing ptr/Storage annotations and proof-only receipt.
- **FORMAL-LEMMA:** raw footprint conservation, package frame/exactly-once installation, old-fact/occurrence death, freshness/history, conservative erasure and negative controls.
- **FORMAL-SCOPE:** singleton fixed root and root-level active sum; Storage-based raw handoff; general descendant/Allocation/metadata protocols are omitted without blocking the bounded target.
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION:** no new finding in inspected Draft 17.9 rules or prior encodings. Canonical is unchanged.

No source syntax, production relocation, byte-copy/memmove algorithm, numeric machine address model, allocator/deallocator, concurrency, GC algorithm, Pin system, FFI/LLVM, M9/F2 or later milestone is implemented. Atomicity means a public relation with complete pre/post states, not concurrency atomicity. A fully well-formed rootless/raw half-endpoint cannot be exposed as a legal move.

## Validation and review evidence

Lean/Lake **4.34.1**, elan **4.2.4**, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, manifest, bootstrap and workflow pins are unchanged. Project-only clean `lake build` passed (729 jobs); `bash scripts/check-proofs.sh` passed, validating the imported production/control closure. All **757** baseline declarations remain in order; **77** public additions give **834** audits. Project-owned Lean source has no proof placeholders/custom semantic assumptions; allowed logic remains exactly `propext`, `Classical.choice`, `Quot.sound`.

**CI result evidence:** [Issue #16's Track: F review handoff](https://github.com/wakairo/NewLang_FormalProof/issues/16) records the open PR, current head SHA and API-verified `pull_request` Lean proofs run/job result and links. The committed unchanged workflow installs pinned tooling on a fresh runner and runs build/audit. READY FOR REVIEW is issued only after that exact-head run completes successfully. The PR remains open and unmerged. No M9, production relocation or further milestone starts.
