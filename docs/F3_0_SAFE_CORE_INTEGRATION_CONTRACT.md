# F3.0 — Bounded Safe Core Integration Contract

Track: F

**F3.0 CONTRACT READY FOR REVIEW**

This is an English companion to the [Japanese primary contract](F3_0_SAFE_CORE_INTEGRATION_CONTRACT.ja.md). It specifies a future theorem target and one bounded F3.1 recommendation. F3.0 adds documentation only: none of the new global checking, execution, function or loop declarations described here have been implemented or proved.

## Authority and resolved prerequisite

Compiler main is `eda75ad09a73cacd0a78d1a0496aa0a86bd77a32`; `CURRENT_SPEC.md` points to Draft 17.17. FormalProof base is `70aae8b9d945db7808f666e58fa31aa4dc9ef000`. Compiler development process, Semantic Sync #99, M9.15 #100 and the updated Coordination instruction on [Issue #22](https://github.com/wakairo/NewLang_FormalProof/issues/22#issuecomment-6028837854) govern this work. F0–F2 and F3.0-pre #23 are CLOSED. Baseline build passes (773 jobs) and all 985 declarations pass the unchanged standard-logic audit.

The [#23 rich lifetime adapter](F3_0_PRE_SUM_LIFETIME_ADAPTER_REPORT.ja.md) resolves F3-IF-1 within one live root, one explicit region and one active responsible claim. Rich take/destroy derive post well-formedness from pre invariants, raw input and an exact surviving-ended-fact guard. They preserve dependency data, end root/occurrence/payload facts and conserve the exact root-to-slot responsibility. Rich legality projects to coarse legality. The converse is machine-checked false.

First Safe Core rich sums are **already-live/preinitialized**. Use #23 for bounded rich take/destroy and F1.4 for flat initialize. Rich initialize and rich by-value destination/root binding remain later **FORMAL-SCOPE**. Precision-losing erasure never authorizes a rich operation.

## Property and architecture decisions

Choose **preservation plus separately modeled no-fault**, rather than preservation alone or total progress:

```text
WellCheckedCore(P, I, E)
∧ InitialSafe(I, E, cfg0)
∧ RawExecPrefix(P, E, cfg0, trace, cfgN)
-------------------------------------------------------------
GlobalSafe(cfgN)
∧ NoModeledSafetyFault(trace)
∧ ResidualChecked(P, cfgN)
```

Raw execution contains successful primitive candidates and fault attempts. It does not assume post well-formedness or legal steps. Fault events independently describe stale/invalid access, dead survivor dependency, affine/discard violations, invalid lifetime/freshness, missing/duplicated responsibility, scope escape and invalid control. No termination, liveness, allocator success, whole-language safety or hardware/raw-byte correctness is claimed.

Choose **C: adapter/refinement theorem network**. A giant unified state would rebuild the kernels; an independent product would duplicate owners without coherence. Keep one authoritative state per profile and derive views:

```text
checked core -> control/call frames + finite sealed memory capsules
  Flat:  Occupancy.State    -> Backing.FlatState -> F0.State
  Fixed: F1.CurrentState    (semantic-only)
  Rich:  Occupancy.SumState -> Backing.SumState -> Conditional.State
                              -> #23 lifetime adapter
                              -> one-way erasure sanity
  F2: one Flat header view + literally unchanged side frames
  F1.5: optional extension adapter
```

Capsules have disjoint byte footprints, nominal identity/domain ownership and capsule-local dependencies. Cross-capsule transfer, aliasing or dependencies are outside the first subset. Call frames refer to authoritative carriers and claims rather than owning duplicate copies. Frame/loose-carrier correspondence, partition coherence and control typing are new proof obligations. Existing public kernels remain unchanged.

## Exact subset and limits

| Included | Bound |
| --- | --- |
| Named functions/direct calls | Finite monomorphic signatures, acyclic call graph, actual checked bodies and same-capsule memory |
| Flat lexical transfer | Explicit source take/destination slot-backed initialize, affine move, unchanged dependencies |
| Fixed current-state operations | Finite fixed-support replace/store/swap; semantic-only, no arbitrary physical embedding/lifecycle |
| Closed sums | Root-level opaque payload, whole/payload update, same/distinct whole swap; preinitialized |
| Rich end | #23 single-root/region/claim take/destroy, including external loose survivors |
| Flat raw/typed memory | Existing bounded backing/layout/access and exact Storage/slot/root accounting, flat lifecycle and updates |
| LifetimeDomain | Flat transfer/finalize with actual survivor guards; rich/fixed domains framed live |
| Ptr/ref | Exact token provenance and operation-local acquisition/use; no persistent ref binding/return/join |
| Finite control | Seq, Boolean If, closed-variant observer Match, separate Return/normal exits |
| Loop | One nonnested F2 loop, zero/one affine parameter, one availability, one mutable outer Copy fact, at most two edges per exit class |

Exclude rich initialize/by-value new rich binding, nested sums, arbitrary aggregate/sum embedding, full borrowed/consuming match and payload-ref issuance, complete P7 ref-result joins, cross-capsule effects, nested-loop composition, recursive SCC, callable/generic/Array-span, arbitrary unchecked/dynamic-container bridge, source frontend, FFI/modules/concurrency, production and backend correctness. Relocation is optional.

Global invariants combine local carrier/place/incarnation/package/domain/dependency consistency, fixed/current structure, occurrence shape and identity, backing/placement, exact scoped byte responsibility, frame ownership and control coherence. Histories are proof-only ghost invariants. Freshness, applicability, access, survivor and scope guards are local preconditions; unchanged data, frame, freshness/history and footprint conservation are postconditions. F2 H is a static certificate, not concrete runtime memory. F1.5 invariants belong to the extension. Source/backend claims are outside the base.

## Checking, calls, control and F2

Select a **declarative checking derivation**, with proof-carrying AST possible as its representation. Reject per-step assumptions of legality. Symbolic resource states retain exact ownership, alternatives and blockers. Static rules establish concrete guards once; representation and subject reduction transport them through actual execution. Existing legal-step post-WF projections cannot substitute for this bridge.

Statement/control small-step uses raw atomic primitives. Runtime selects one If/Match arm; checking verifies all statically reachable arms. Normal joins are static alternatives. Return, Continue and Break are separate outcomes; zero normal exit does not manufacture a successor.

Function signatures specify parameter/result ownership and effects. Flat owned parameters initialize explicit callee slots; return takes them into loose result carriers. Caller memory and survivor dependencies remain in the same authority. Actual body derivations, caller-visible effects, callee-local closing and no escaping ended dependencies are required. Rich roots can be caller-owned access operands, but calls cannot secretly initialize rich parameter/local roots. Operation-local access operands are not a proof of complete source-level persistent ref parameters.

F2's `body` must be instantiated from actual checked core body execution. Entry representation, complete Continue edges, post-fixpoint H, exact affine/availability constraints, fresh iteration closure and separate Break/Return checks derive its transfer premises. Import arbitrary finite Continue coverage and finite Break joining. Zero Break yields zero normal result.

The loop adapter permits a flat carry/current-value slice only. Other flat data and all rich/fixed capsules are unchanged frames; their dependencies must not target the mutated outer fact. Occurrence-dependent loop carry is excluded. Rich blockers are preserved in authoritative side frames, never erased to fit F2's ordinary fact vocabulary. Unknown/widening preserves blockers and cannot widen exact availability.

## Trust and refinement boundaries

Mixed privilege policy: arbitrary unchecked/external mutation and dynamic-container bridges are excluded. Geometry/backing provision, alignment and representation are explicit initial environment contracts; exact local access/ending authority must come from capability context or a displayed operation-specific external obligation. None may contain post-WF or whole-body safety. General allocation/deallocation is not proved.

Relocation needs a separate adapter relating F1.5 `accounted` and annotations to the selected rich capsule, proving raw guard-derived safety, footprint/freshness and framed coherence. Do not force its fields into every base program.

**A: formal Safe Core soundness does not imply B: production checker correctness or C: backend correctness.** Future B requires `ProductionAccepted`, `FormalizesAs`, a source/core semantic refinement and a formal checking derivation. Future C requires simulation preserving control, affine carriers, exact facts/incarnations/occurrences, authority/access, responsibilities and visible effects. A hypothetical checker that drops an occurrence dependency violates B; a lowering that retargets a stale identity violates C.

## Stress tests, findings and handoff

Primary contract §13 covers all W1–W15: owned flat call/update/return; guarded domain end; exact raw lifecycle; stale ptr restart; sum dependency and bounded ref exclusion; caller effects; all-arm checking/one-arm execution; Return/normal separation; F2 prefix and zero-break handling; excluded recursion/unchecked; optional relocation; independent production/backend failures.

Reject tautological legality-based checking, safety-by-reachability, opaque SafeCall/SafeLoop/SafeUnsafe assumptions, incoherent products/reverse erasure, blocker-dropping joins, runtime execution of both arms and an empty-only theorem. New guard/control/frame adapters are specified integration proof obligations, not already available proofs. F3-IF-1 is resolved. New canonical hole/ambiguity/extraction error: none found. Representation choices are non-normative. Precision exclusions are FORMAL-SCOPE. Targeted external research is unnecessary; no new M/P/R work is started.

**Exactly one recommendation: F3.1 finite Seq/If + one ordinary direct-call scaffold + selected flat/rich lifetime adapters.** Primary §15 fixes its files, imports, theorem concepts, witnesses, audit and stop condition. Bound: entry plus one nonrecursive callee, call depth one, at most one owned flat parameter, unit/Bool/loose-value result, one Flat or Rich authority per instance. Flat has one region and at most one caller/callee slot each; Rich keeps #23's single-root/region/claim bounds and no rich initialize. No loops, Match, fixed aggregate, domain finalize, relocation or full ref joins in this pilot.

Prove actual checking-to-guard/raw-candidate safety, selected-arm soundness, affine parameter/return transfer, caller survivor and callee escape safety, step preservation/no-fault and finite-prefix safety. Require nonempty flat call/update/return and rich take/destroy controls, plus negative branch/copy/discard/extent/staleness/dependency/escape/erasure tests. Audit all additions while retaining the 985 declarations and whitelist. This pilot is not completion of the full first Safe Core.

Final documentation-branch build/audit and exact-head PR-event `Lean proofs` CI evidence are recorded in the [Issue #22 Track: F handback](https://github.com/wakairo/NewLang_FormalProof/issues/22). Pins, Lean, audit and workflow remain unchanged. Leave PR and Issue open/unmerged. Stop at **F3.0 CONTRACT READY FOR REVIEW**; do not begin F3.1.
