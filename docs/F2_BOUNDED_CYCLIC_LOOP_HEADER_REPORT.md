# F2 — Bounded cyclic loop-header formal kernel

[日本語（primary report）](F2_BOUNDED_CYCLIC_LOOP_HEADER_REPORT.ja.md)

F2 implements FormalProof [Issue #19](https://github.com/wakairo/NewLang_FormalProof/issues/19). Compiler development process was read before authority/baseline checks. Canonical Compiler main is `2a3643449ae5d9fa619909c9fa16d21b8d2ac5e6`, CURRENT_SPEC selects **Draft 17.16**; FormalProof base main is `a3a8c70becb3da6a9c2fc6f91ca578f49b19df32`. Both current mains were checked and match the handoff. F0/F1 source and public statements are unchanged. The historical local Draft 17.4 is unchanged and is not current authority.

## Model and boundary

`ConcreteHeaderState` is a bounded concrete language-state slice, with zero/one non-Copy parameter, one captured outer non-Copy availability, and one outer Copy current-value component. Concrete fields never contain Unknown or a widened origin. A `Signature` fixes count/slot/type correspondence and entry availability. `HeaderWellFormed` checks exactly one affine carrier, live dependencies, iteration-scope exit and recorded identity histories. Stable external facts cannot freeze an old fact of the modeled mutable Copy place: `externalSeparation` excludes that place from `publicFacts`; current facts use the separate current-value branch of `FactLive`.

`AbstractHeaderState` is proof information **H**, with may-origins, hidden dependencies and current facts. `May.unknown` contains every alternative. `Represents` combines the exact layer with may-set membership. Symbolic origin Unknown represents unbounded concrete fresh packages without duplicating any concrete responsibility. `Widen` preserves the signature and includes every may-alternative. No lattice order on captured availability is provided. Unknown cannot remove a safety blocker; losing correlations may reduce acceptance precision.

The existing `F0.PackageId`, `PlaceId`, `ValueFactId` and `Fact` are reused. F2's `Package` is the small static-type/dependency/identity view, not a replacement of F0/F1 runtime values. `BindingId` is distinct from package/incarnation identity. `Dependency.externalFact` wraps the existing fact, while `.iteration` records a dependency on the ending iteration; persistent ptr provenance is not automatically a blocking dependency. Finsets, IDs, zero/one slot and histories are non-normative. `usedBindings`, `usedPackages`, `usedFacts` are proof-only; witness max-plus fresh supplies do not require compiler/runtime counters.

`Loop.edges` is a finite, statically supplied family (at most two indices in each continue/break/return class). `Loop.body` is the explicit ordinary transfer premise: expression evaluation, Copy assignment, resource consumption/production, acyclic calls and function return obligations must be justified by a future body checker. This proof does not synthesize a body checker, authorize arbitrary destruction, prove every canonical program safe, or erase full relocation geometry into F2. Abstracting body semantics is independent of the proved header/backedge/exit obligations.

## Induction and affine/current-value results

`Continue` requires a supplied continue edge, body relation, well-formed endpoints and `ContinueFrame`. A fresh iteration binding receives either exactly the unchanged package P or a fresh same-type transformed Q. The exact carrier set removes the old responsibility; type equality does not equate package identities. All ghost histories are monotone. A changed Copy current fact is historically fresh; its old fact is non-live. A surviving package's hidden dependency on that old fact still rejects the candidate.

`PostFixpoint` contains entry and closure over **every supplied legal continue edge**. `Trace` covers arbitrary finite edge lists; `Reachable` is their inductive closure. Theorems prove finite-trace/reachability equivalence and sound representation of every finite sequence. No termination, least fixed point, exact package-ID enumeration or production widening algorithm is assumed. The two-edge concrete fixture proves existence of a legal trace for **every list of its two indices**, not just a conditional soundness theorem over an empty transition relation. Both edge alternatives affect hidden dependencies, package origins and current facts.

An unchanged non-Copy fixture retains its external hidden dependency through arbitrary traces. Transformed carries replace P with fresh Q. A no-affine-slot fixture changes the outer Copy component as a counter-like cyclic state (it does not model arithmetic counter payloads). A genuinely larger inductive H represents an extra valid state outside reachability, and remains sound.

## Exit results

Only continue contributes to header recurrence. Break and return are distinct relations/outcomes. `breakEdges` is the finite **static index set**, not a finite enumeration of runtime result identities. `IndexedBreakBound` analyzes each reachable break under the established H; `FiniteBreakJoin` includes those summaries with common static type, Copy capability and captured outer availability. `finite_break_join_sound` proves coverage of normal results. Hidden dependencies/current facts/origins remain alternatives. The concrete exit fixture selects fresh package/current-fact IDs from each header history, and the finite edge summaries use Unknown for those unbounded runtime identities; they do not reserve a fixed result ID that later iterations could reuse. Copy and non-Copy exit slices have different static TypeIds. Copy results can join; non-Copy results at the same type can have different package IDs, each with one concrete carrier. Break availability may differ from entry; all break alternatives agree at the result join. `ExitFactsLive` and scope checks retain surviving blockers.

Return belongs to the function-exit path and never feeds H or the normal break-result set. A zero-break loop has no normal result at all, even when continue and return edges exist. It does not synthesize Unit, bottom or never. All supplied static edges are retained; no incidental runtime value is used as a constant-propagation proof.

## Verification and disposition

Baseline: pinned `lake build` and all **834** existing audits pass on base main. All previous audit entries are preserved in order; **96** F2 public declarations are added, for **930**. Two private fixture helpers are dependencies of audited public proofs. No project Lean source uses proof placeholders or custom semantic assumptions. Allowed dependencies remain `propext`, `Classical.choice`, `Quot.sound` only. Lean/Lake **4.34.1**, elan **4.2.4**, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, manifest, bootstrap and CI workflow are unchanged.

Validation commands: `lake clean newlang-formal`, `lake build`, `bash scripts/check-proofs.sh`. Exact commit, PR URL and **pull_request-event Lean proofs** run/job result are recorded in the final **Track: F** handoff on [Issue #19](https://github.com/wakairo/NewLang_FormalProof/issues/19), after local validation and CI. This pointer avoids a self-referential report commit hash; Git is change history. PR and Issue remain open, unmerged/unclosed; stop at **F2 READY FOR REVIEW**, for Coordination review / Semantic Sync.

## FORMAL findings and scope

- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION: none found** in the inspected canonical clauses. No canonical document was modified or strengthened to repair a failed proof.
- **FORMAL-ENCODING:** orthogonal bounded control-flow state; existing nominal identities; exact layer plus may/Unknown abstraction; ghost freshness and static edge-indexed finite exits. No full F1.5 erasure is claimed.
- **FORMAL-LEMMA:** inductive post-fixpoint covers arbitrary finite sequences, preserves exact affine/availability/scope obligations, and widening retains safety blockers; finite break summaries are analyzed after H.
- **FORMAL-SCOPE:** one loop with the explicit bounds above. Nested loops would use nested kernel instances; composition is not proved here. Acyclic body-sensitive calls are abstract transfer premises, not verified call summaries; recursive SCC is excluded. No exact source grammar, parser, production implementation, M/P/R work, relocation changes, FFI, LLVM, modules or concurrency. No subsequent milestone begins.

The Japanese report below contains the exact 96-declaration / clause inventory and the 15-control and 8-positive acceptance mapping.
