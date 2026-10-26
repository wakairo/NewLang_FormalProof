# F72 bounded typed lexical prefix (C50)

Authority: FormalProof main `5437f92d099e228773d31e2323e8ee6228ca21bf`;
Compiler main `38b0954be6b1466a2982e7c58e1070ac76a9fafc`;
CURRENT_SPEC selects Draft17.34.
P927 `94c8d18d368a95d02d234d114ab4461e22048842` remains private/HOLD.
F71's contracts are inputs to this work plan, not previously checked proofs.
R928 remains STOP/INCONCLUSIVE; F70's limited private Gate A is not a public proof.

## Contract and construction (B only)

`NewLang/Adjunct/LexicalPrefix.lean` defines a bounded typed AST:
one complete, nonrecursive nominal with exactly two distinct named u8 fields;
two distinct lexical binding names; an arbitrary block instance; two complete
literal aggregate initializers; arbitrary u8 payloads; and arbitrary
permutations from initializer source positions to declaration indices.
The target usize width is positive and parameterized, and both usize operands
carry their actual range proofs. Equality and less-than comparisons are supported,
with either true or false outcome. No particular producer fixture, numeric IDs,
payloads, names, order, or 64-bit width are selected.

The evaluator executes block entry, the first complete initializer/binding,
the second complete initializer/binding, left and right usize literals, comparison,
temporary termination, and the common pre-arm cut. No IF arm executes.
The initial dynamic state is empty. Binding events create installed aggregates
and three node records each: one original whole root and two member children.
Creation tags consist of this evaluation's block instance, binding ordinal, and
whole/field path. Their uniqueness is local to this empty-history evaluation;
this is not freshness relative to an arbitrary preexisting program state.

`LexicallySupported` requires active block membership, the block-entry event,
the binding event, and continued installation of the original aggregate.
`lexical_support_derived` proves these from evaluation; support is not a
formation assumption. This support records lexical extent only. It is not
an explicit nonCopy LifetimeDomain value, read/write stability token, pointer,
Allocation, or rich Domain/carrier witness. The state and evaluator expose
no operation issuing any of those privileges. The helper functions describe
this bounded evaluator, not a validated transition API for arbitrary states.

Checked theorem targets include:
- exact installed aggregate/root/node lists, two roots and six nodes;
- distinct binding sites and unique node, incarnation and current-fact tags;
- initializer source-position/declaration-index inverse correspondence;
- root aggregate ownership and dependent member carriers, with no child as root;
- empty literal dependencies and active lexical support derived from history;
- target-width ranges, both known-condition outcomes, ended temporaries/common cut;
- the bundled parametric `typed_prefix_evaluation` theorem.

The empty dependencies are a rule of this literal-only AST, not a claim about
arbitrary reads, calls or aggregates. Incarnation/current-fact wrappers are
adjunct creation tags, not secretly minted accepted-rich permissions.
These statements are proved from typed AST formation and definitions, without
rich WellFormed, expected POST, saved entry, private status, actual plan,
F62.Call.body, or a compiler/source-issued Change assumption.

## Limited C representation definition (C, unproved against implementation)

`Encoding` specifies separate injective node/incarnation/fact maps.
`observe` projects generated roots, ordered node rows, original owners, scalar
values/dependencies, active blocks, known condition, temporary state and common cut.
`Represents` states existence of such an encoding for an observable entry.
This deliberately limited relation is only a definition. No actual C snapshot,
registry, parser or semantic primitive is proved to satisfy it. It does not
encode the whole compiler entry or establish trace simulation, owner lifetime,
raw-source authenticity, machine-integer serialization, or native behavior.
A later producer must supply and independently justify those correspondences.

## Accepted-rich discriminator (D remains HOLD)

`live_roots_empty_domains_not_wellFormed` uses accepted
`F1.WellFormed.domainsValid`: nonempty live roots with no live Domains cannot
satisfy F1.WellFormed. No rich state is fabricated in this module.
Adding an arbitrary ghost governing Domain, package or Domain-value carrier
would satisfy neither source origin nor lifetime/ending-authority obligations.
F1 also requires domainCarrierCoherent; mathematical tags or a host owner pointer
alone do not supply its source interpretation.
Conversely, this obstruction does not prove ordinary lexical source invalid:
it identifies the missing interpretation, not a language contradiction.

## Unresolved boundaries and next minimum

A: raw NewLang source/parser/registered-plan authenticity and faithful elaboration
to this typed AST are unproved.
B: the bounded mathematical evaluator is the only theorem implemented here.
C: actual observable compiler fields and their original ownership/replay history
are not proved to refine the relation.
D: lexical support, installed aggregate/member carriers and creation tags have
no proved interpretation in accepted-rich lifetime/authority. This remains HOLD.

The next minimum is a Coordination-selected, bounded fidelity contract from
one ordinary typed lexical source prefix to this AST and the observable relation,
with original binding/field identity and source order preserved. Separately,
choose/prove the ordinary lexical lifetime interpretation before any rich lift.
Do not make expected POST, private entry status, F62.Call.body or arbitrary
Domain/carrier witnesses inputs. Do not expand to calls/loans/Change/join/native.

## Validation boundary and value alignment

The new module is imported by NewLang.lean and hence by the pinned Actions build.
Existing workflow, bootstrap, toolchain, manifest, accepted F0/F1 definitions and
the audit script are unchanged. The existing script builds the new module and
audits its preexisting declaration list. Module-level `#print axioms` commands
add explicit dependency reports for the new bundled proof, freshness/identity,
condition/range, ownership and accepted-F1 discriminator theorems to build logs.
Actual CI results, failures, commit and run/job links belong in the terminal
Issue report; this note is not a declaration that an unrun build passed.

Gate A: https://github.com/wakairo/NewLang_FormalProof/issues/72#issuecomment-6405813877
CI budget: at most three natural runs, no manual retry. At most one mechanical
repair after retaining the first failure; open one DRAFT PR only after branch green.

VALUE-ALIGNMENT-RISK (separate from technical B results): a mathematical lemma
does not demonstrate reduced author/caller UB audit closure relative to
well-factored C. More private retained-unit/reparser/test machinery may increase
trusted maintenance without proving ordinary CLI source authority. This adjunct
tests one necessary reusable prerequisite; it is not Product GO. Product GO #624
is PAUSED and H1 #268 remains HOLD. Compass is navigation; Product Value Strategy
§§1.1/1.3, Development Process §§4.2/4.3/4.3.2, DDP and DI006/007/011/017 govern
the scope. Keep Draft17.34, replace nothing, defer full rich interface and new
public issuers. No compiler changes, merge, or other Track is authorized here.
