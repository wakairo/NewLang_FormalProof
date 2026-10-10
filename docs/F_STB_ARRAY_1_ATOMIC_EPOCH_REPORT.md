# STB-ARRAY-1 allocator epoch exchange: bounded independent experiment

Track: F — FormalProof Issue #45.

**HOLD — UNPROVED CRITICAL COMPOSITION/ASSUMPTION.** A constructive finite
projection admits a conservative single-current-epoch exchange. It satisfies
its affine/metadata/history invariants and the accepted physical invariant.
This is not a proof that libc realloc, the existing relocation kernel, or an
admitted NewLang source operation implements that exchange. The missing
allocator/rich-claim reconstruction boundary is substantive.

## Authority, evidence, and process

- Fixed FormalProof base/main: `2ae7cc7b88dfaf9e07518fa79f968f5ab2f60d41`.
- Fixed Compiler main: `b75baea96a644e68634baee383299b66981b3c62`.
- `Compiler/docs/reference/CURRENT_SPEC.md`: canonical Draft 17.30.
- Read Process §§3–4.2, Design Decision Procedure, Design Intent Ledger
  DI-009–014 and the dynamic/raw/span history indexed by M's report. Historical
  design gate: **N/A — non-selecting finite proof research**, not adoption of a
  new source operation, provisional API, or normative rule.
- Read M #263's research and Coordination acceptance, P #265's actual C17
  execution report and Coordination adjudication. M's local adapter remains a
  hypothesis. P is a reported remote C reference, not this F executor's replay.
  Its complete binary/log archive was not independently retrieved here.
- P reports GCC14.2/Clang19.1 strict C17, H32/E8, requests 64/96/160 and cap4/8/16.
  Default libc reused numeric addresses; FORCE moved physically twice. ASan /
  UBSan passed with LSan scanning disabled; LSan-on attempts failed. No C OOM
  oracle or LeakSanitizer-clean evidence is inferred.
- Git fetch initially yielded a stale main ref while REST main matched the fixed
  SHA. The branch was created explicitly from the fixed SHA; no alternate base
  or accepted theorem was substituted.

Relevant canonical anchors: §3.1 independent live BackingRegions cannot share
abstract byte instances; §§3.2–3.3 exact original Allocation/full raw Storage;
§§10/13/14 current identity and domain stability/ending; §15.1 origin-rooted
responsibility (metadata is evidence), §15.2 private transition/failure
responsibility, §15.3 unselected surface; §24.3 raw bytes versus typed move;
§24.4 exact `(R,range)` same-place and no fallible work inside root relocation;
§24.5 raw claims; §§25.3–25.12 current nonescaping contiguous spans.

## Finite model: explicit construction, no post-WF oracle

`NewLang/Adjunct/ArrayEpoch.lean` is an isolated **unselected** local transition
experiment, importing accepted F1.5 proofs. `Epoch` contains generation, address,
capacity and governing D. R/A/K are distinct nominal labels for one generation;
addresses are observations, not provenance. The generation is ghost bookkeeping,
not a runtime counter or owner registry. Capacities are limited to 4, 8 and 16.

State contains one optional current epoch, a separately checked singleton owner
credit, an ordered live affine package list, explicit returned package custody,
len/cap evidence, used-epoch history, a release ledger, scoped domain loans, and
explicit ending-domain availability. Each current element gets an independent
incarnation/token `32*generation+i`. History conservatively reserves a block of
16 possible identities for each used epoch; it overapproximates allocated
incarnations and is not a runtime element bitmap.

Header is explicitly **raw-owned**, not a secretly live typed Header root.
Its 32 bytes, the `8*n` typed prefix and `8*(cap-n)` vacant tail partition exactly
`32+8*cap`. Empty tail is a zero-byte *set of responsibility*, never a fabricated
zero-length Storage value. n=0 is an already allocated backing with no element
roots, not a claim that an empty array requires a dummy backing.

`Grow` requires pre-WF, the exact current epoch, all scoped loans closed, ending
authority for the original D, a history-fresh new generation, supported larger
capacity. It contains **no post-WF or conservation conclusion**. `candidate`
explicitly replaces the current owner credit, records old consumption, retains
all prior history, transports the ordered packages unchanged, and derives new
root identities from the fresh epoch. `execute` has two separate outcomes:
failure returns the entire input state; success uses this constructor.

Derived theorems include:

- `grow_preserves_wellFormed`, `all_outcomes_wellFormed`;
- `successful_grow_transports_values_exactly_once`,
  `successful_grow_consumes_old_owner`, `history_monotone`;
- `grow_preserves_governing_domain`,
  `fresh_elements_have_new_incarnations`,
  `new_incarnation_not_historically_allocated`;
- `old_ptr_cannot_be_reacquired`, `fresh_root_is_current`;
- exact header/live/vacant partition, size equation and disjoint element ranges;
- affine `takeAll` to explicit returned custody, free only after no live child /
  scoped loan, and non-repeatable exact current header-base consumption.

These are semantic token/list operations, not a theorem that bitwise memcpy
transfers arbitrary nonCopy packages. The real Rec is Copy; opaque affine IDs
are a finite ownership stress test. General dependent payloads/destructors are
not covered.

## Accepted-kernel connection and critical boundary

`ArrayEpochPhysical.lean` constructs complete finite physical placements for
all n elements, then proves **accepted** `Backing.PhysicalWellFormed`: singleton
live backing, exact live locations, extent containment and pairwise disjoint
8-byte element roots. `grow_has_accepted_physical_post_invariant` derives it from
Grow; `current_root_has_exact_physical_location` connects current tokens to that
geometry. The model's address-to-byte mapping is one selected finite geometry,
not a universal equality law between addresses and abstract byte identities.

Accepted-kernel facts are proved independently of the proposed exchange:

- `accepted_relocation_preserves_backing_world`: every F1.5 RawRelocate keeps the
  backing world. Existing relocation alone therefore cannot implement the epoch
  exchange (`changed_world_is_not_an_accepted_relocation`).
- `same_place_cannot_change_current_state`: accepted same-place relocation is
  identity, not changed-capacity allocator exchange.
- `accepted_typed_move_keeps_package_data`: existing typed movement preserves
  value/owned-annotation data and moves the package, unlike semantic raw copying.
- Independently live aliased byte sets violate accepted `RegionsDisjoint`.
- An old source placement in a backing no longer live violates accepted
  `PhysicalWellFormed`; numeric address equality does not repair its entry.

**Missing composition:** a concrete allocator outcome must reconstruct new
origin-qualified Allocation/K/full-raw responsibility and rich element claim /
lifetime / package state without using either aliased simultaneous regions or
an already invalidated old source. There is no such adapter or implementation
refinement in this PR. One cannot derive it from the projection's preservation
or from a successful libc return.

## Positive witnesses and exact ledgers

`Counterexample/ArrayEpoch.lean` uses D7, package id i/data17*i+3 and these finite
stable points:

| Point | Current K/A/R epoch | Live O indices | Old consumed epochs | Bytes |
| --- | --- | --- | --- | --- |
| n4/c4 | generation1, address1000 | 32..35 | none | 64 |
| n4/c8 | generation2, address1000 or2000 | 64..67 | 1 | 96 |
| n8/c8 | generation2 | 64..71 | 1 | 96 |
| n8/c16 | generation3, address1000 or3000 | 96..103 | 2,1 | 160 |
| n12/c16 | generation3 | 96..107 | 2,1 | 160 |
| take-all/free from n8/c16 | none; values explicitly returned | none | 3,2,1 | none current |

n4 growth and n8 growth each have a real Grow proof and derived WF. The extra
four-package initialization checkpoint is **reconstructed**, not a machine-
checked push/source trace. The same is true of n12. The n0 allocated case has a
legal Grow and no fabricated elements. Both FORCE allocate-before-end worlds
(64/96 and96/160) have accepted RegionsDisjoint proofs. Same-numeric-address
success has fresh R/A/K and element incarnations; old ptr/span descriptors cannot
be reused, while fresh current root/count conditions hold.

Failure preserves the **entire** pre-state and its old permitted token, metadata
4/4 and owner. This is a separate hypothetical NewLang-side outcome; original
stb realloc NULL handling is not used as its success/failure oracle.

Final free witness starts with eight current values after the grow and explicitly
takes all to result custody before consuming epoch3 once at header address1000.
It proves no implicit discard. It is **not** the stb deletion/pop suffix. The
n12 read id7/122 theorem is a data-policy check, not a native read oracle.

## Negative controls and classification

| Control | Machine-checked result | Boundary |
| --- | --- | --- |
| two simultaneous full alias epochs at same physical prefix | RegionsDisjoint impossible | accepted kernel §3.1 |
| realloc first, then use old source in ended R | PhysicalWellFormed impossible | accepted kernel source-liveness |
| changed R/range chosen as same-place | different R and size; same step is identity | accepted exact-location rule |
| active span/coarse D loan across growth, even ending authority present | Grow impossible | proposed bridge guard reflecting §§14/25 |
| old ptr at same address / old span descriptor | no CurrentRoot/CurrentSpan in new epoch | finite identity projection |
| metadata len5/cap8 with only four actual values | bounds pass; no fifth root, WF fails | proposed live-prefix reconstruction, §15 principle |
| missing old owner on failure or missing new owner on success | WF fails | proposed single-owner bridge |
| duplicate Allocation release / second final free | WF or Free impossible | proposed affine ledger |
| wrong original backing at free / item pointer as base | Free / FreeAt impossible | proposed origin/base bridge |
| wrong D ending authority | Grow impossible | proposed domain guard |
| live child ignored at teardown | Free impossible | proposed raw-recovery guard |
| duplicated nonCopy payload by raw-copy interpretation | active size/metadata invariant holds, affine uniqueness fails | proposed token projection, §24.3 principle |
| historical epoch reused | Grow impossible | proposed conservative freshness history |

These are proved propositions, not source checker results or intentionally
executed C UB. Most local guards are **not claimed as integrated accepted rich
kernel theorems**. Existing-kernel controls are identified separately above.
Incorrect order/checksum policy is separate from lifetime safety.

## Separately counted implementation / integration obligations (six)

No custom proof assumption is added to Lean. Nevertheless these six external
obligations remain before the experiment could justify an allocator mechanism:

1. Actual failure must leave original backing, authority, bytes, metadata and
   permitted handles intact, with no hidden success/partial consumption.
2. Actual success must realize the modeled atomic owner/epoch handover, publish
   no aliased dual live region, and expose no callback/reentrant intermediate.
3. Actual semantic value transport must preserve bytes and rich value-owned /
   dependency annotations, end all old lifetimes and issue fresh roots exactly
   once. The opaque package IDs here are not that representation theorem.
4. The domain-ending inventory and closed-loan evidence must correspond to real
   capabilities, including all surviving refs/spans and external dependencies.
5. Real geometry/access/alignment/overflow/platform semantics must refine the
   selected H32/E8 geometry. Request arithmetic here uses unbounded Nat.
6. Reconstruct and refine full rich F0/F1 semantic, raw claim, hidden owner and
   exact full-Storage recovery state, including framed external roots and final
   D disposition. Physical projection alone does not establish these interfaces.

The experiment has no recoverable work *inside* an accepted §24.4 root move.
Fallible allocator choice belongs to the proposed larger private boundary.
Treating it as an existing root relocation, or simply declaring the above six
obligations true, would be an invalid positive conclusion.

## Scope / findings / handoff

FORMAL-ENCODING: constructive projection and physical invariant are compatible;
nominal epoch and root history are separate from numeric addresses and metadata.
FORMAL-LEMMA: finite conservation/freshness/failure/physical proofs and explicit
alias/stale-source countermodels are machine checked. FORMAL-SCOPE / missing
formal adapter: six obligations above, general nonCopy payload dependencies,
actual pushes, ordered delete4..6, moves7..11→4..8, pop11/190 and its exact
8-survivor teardown remain **UNPROVED**. No suffix composition is advertised.

No old canonical legal-source counterexample establishes FORMAL-HOLE or
FORMAL-AMBIGUITY. Tempting numeric-same no-op / alias mint proposals are refuted,
not selected. No global owner system, per-element runtime bitmap, general Vec,
source/API/Draft/DI selection, Compiler/backend/FFI change or native product PASS.

Minimum future design question, not a launched Track: can one localized allocator
contract discharge the six obligations—especially same-address success—without
relaxing §3.1 or inventing metadata authority? Until then HOLD. Human risk is
concentrated in allocator atomicity, complete claim recovery, rich dependencies
and target layout rather than consumer-side bounds arithmetic.

Frozen original cJSON North Star remains PASS/FAIL UNDECIDED and original B
separate-recipient implementation STOP/REASSESS. Neither metric is modified.

Baseline: build +1568 audits PASS. Candidate: build +1652 audits (1568 retained,
84 added), standard Lean logic whitelist unchanged, no proof placeholders or
custom semantic assumptions. Lean4.34.1/mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; pins, accepted theorem meanings,
README and CI unchanged. Exact candidate head / OPEN-unmerged PR / Actions
results are recorded in the Issue #45 handoff. Git is the change-history source.

F STB-ARRAY-1 ATOMIC OWNER-EPOCH EXCHANGE: HOLD — UNPROVED CRITICAL COMPOSITION/ASSUMPTION
