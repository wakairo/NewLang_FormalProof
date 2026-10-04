# F0.5 — persistent ptr / safe ref acquisition

F0.5 verifies the point-of-acquisition reference kernel: a persistent pointer token
can acquire a ref only at its exact current live incarnation, using matching
governing-domain stability evidence and the omitted access obligations. A token
is retained after lifetime end; historical freshness and acquisition-time identity
checking prevent it from reviving when the same site becomes live again.

The starting main is F0.4 merge `941c1df9ae53a3536a9e7315deb1b1d70fea7e54`.
Before edits, `lake clean newlang-formal`, `lake build` and `bash scripts/check-proofs.sh`
passed: 621 build jobs and all 180 earlier theorem reports. F0.0–F0.4 declarations,
State, WellFormed and their theorem statements are unchanged by F0.5.

## Sources and exact representation

Draft 17.4 remains normative and unchanged. Relevant sources are §10/§10.1
(persistent ptr and conversion conditions), §10.2 (scope-independent ptr retention,
without implementing that conversion), §11 (ref scope and write authority limits),
§13.2–3 (incarnation-owned governing relation and ordinary domain stability), and
§14 (initialize results and root lifetime end). F0 bridge §22.1–2, §28 F0.5 and
§30.4 select this subset. §22.3 deliberately defers lexical scope/dependency.

**Formal representation choices are non-normative.**

```lean
structure PtrToken where
  location : RootLocationId
  incarnation : IncarnationId
```

PtrToken is an external mathematical value. Copying or retaining it does not
change State; take/destroy do not remove it. No token registry, second liveness
table, or persistent acquired-ref token is introduced. It contains neither
ValueFactId nor DomainId. Current-value version and root lifetime identity remain
separate. Current governing state is consulted only for the token's exact live
incarnation; a new incarnation cannot retarget an old pointer's relation.

Arbitrary Lean structure construction is not source-level safe issuance, and
Lean equality/DecidableEq is not a source pointer equality operation.
`ptrFromInitialize` constructs the mathematical result value;
`initialize_yields_current_ptr` links it to a successful existing InitializeStep,
its fresh incarnation and exact live location. `initialize_ptr_can_acquire_ref`
proves immediate acquisition when caller evidence/access obligations hold.
No safe pre-lifetime minting or ref-to-ptr operation is introduced.

`CurrentPtr s ptr` means there exists a root at `ptr.location` whose incarnation
equals `ptr.incarnation`. `LiveIncarnation` and `Governs` remain the F0.4 derived
occupancy views. No identities or state invariants are added in this milestone.

## Acquisition relation and assumptions

```text
RawAcquireRef hasStableEvidence canAccess s ptr evidenceDomain:
  exists root:
    s.occupancy ptr.location = LiveRoot(root)
    root.incarnation = ptr.incarnation
    root.governing = evidenceDomain
  hasStableEvidence
  canAccess

AcquireRef = WellFormed s AND RawAcquireRef
```

Acquisition is a Prop derivation, not a pre/post state transition. No persistent
ref result is stored. `evidenceDomain : DomainId` identifies the evidence's domain;
`hasStableEvidence : Prop` expresses the caller's possession of the corresponding
ordinary stability evidence. These are separate parameters: `domain ∈ liveDomains`
does not establish possession of an ordinary domain ref. Domain liveness follows
from the exact target and WellFormed, but neither supplies the evidence premise.
Wrong-domain rejection is checked even when **both** domains are live.

`canAccess : Prop` abstracts valid provenance, originating BackingRegion liveness,
valid initialized representation, alignment, sufficient range and required
read/write access. Callers must instantiate and discharge both propositions for
the state and use under consideration. Production never fixes them universally
to True; only concrete kernel fixtures do. This is a shared read/write acquisition
core, not a derivation of either source-level access mode. Write is not exclusive
ownership or lifetime-ending authority. No ending/exclusive premise is added.

**AcquireRef proves point-of-acquisition legality/current liveness.
It does not yet prove full future-use scope stability.** The domain Prop is an
explicit abstraction boundary, not an implementation of the block-scoped evidence
or its dependent ref. In particular, no theorem authorizes using an acquired ref
across a later end operation; those future-use constraints remain deferred.

## Lifecycle controls and retained tokens

One fixed injective `RootSiteLayout` and `RootLocationId` are used for every
initialize in all lifecycle fixtures. PlaceId is obtained from that same layout.
The fixture table has dependency-free, discardable values; entries without a
carrier are inert. A constant abstract table keeps the fixture small and makes
no finite runtime storage claim.

| Control | Machine-checked result |
| --- | --- |
| Initial vacancy → initialize O1/VF1 | Existing legal InitializeStep issues ptr(L,O1); acquisition succeeds |
| take O1 | Legal TakeStep; retained ptr(L,O1) cannot acquire |
| destroy O1 | Legal DestroyStep; retained ptr(L,O1) cannot acquire |
| take → initialize same L with O2/VF2 | L and place remain the same, O2 is fresh, old ptr rejects and new ptr accepts in the same live final state |
| destroy → initialize same L with O2/VF2 | Same fixed layout/site, old ptr rejects and new ptr accepts |
| replace VF1 → VF2 at O1 | Legal ReplaceStep changes current fact; the same ptr(L,O1) acquires both before and after |
| Live target/domain but no stability/access premise | Acquisition rejects independently |
| Wrong evidence domain, also live | Acquisition rejects |

General stale-after-take/destroy proofs reuse F0.4's incarnation-end lemmas,
not token deletion. The generic reinitialization theorem combines the retained
old incarnation in pre-history with RawInitialize's historical freshness; exact
location/incarnation correspondence then rejects the old token even though
occupancy is live again. Take/destroy lifecycle helpers supply the recorded old
identity from the existing history theorems. Immediate new-token acceptance is
derived from the same legal InitializeStep, preventing vacuous negative proofs.

## Isolated omitted-guard countermodels

All broken definitions are **private** to `NewLang/F0/Counterexample/Reference.lean`.
No production relation or earlier operation is weakened.

1. **Omit only initialize incarnation freshness.** Starting from the successfully
   initialized O1 and a legal take, a private broken initialize uses the same layout,
   same location, incoming loose package, live matching domain, fresh VF2, true
   ordinary authorization/type premises and the unchanged initialize candidate.
   It reuses O1, which is dead but still recorded. Pre and post satisfy all eight
   WellFormed components; all other raw initialize conditions hold. Normal
   RawInitialize rejects, but normal AcquireRef accepts the retained old ptr again.
   Thus state well-formedness alone cannot replace historical allocation freshness.
2. **Omit acquisition incarnation match.** After a normal fresh O2 reinitialize,
   exact location is live and the governing evidence matches. The broken relation
   accepts ptr(L,O1), while normal AcquireRef rejects. Both historical freshness and
   acquisition-time exact identity checking are needed.
3. **Omit acquisition domain match.** A private relation retaining WellFormed,
   exact CurrentPtr and both caller premises accepts evidence for the other live
   domain; normal AcquireRef rejects. Domain liveness alone is insufficient.

## Complete new theorem inventory

Production declarations in `NewLang.F0` (18):

| Theorem | Checked property |
| --- | --- |
| `acquire_ref_targets_exact_location_incarnation` | Exact target root/location/incarnation via CurrentPtr |
| `acquire_ref_implies_live_incarnation` | Target incarnation is currently live |
| `acquire_ref_matches_governing_domain` | Exact root governed by evidenceDomain |
| `acquire_ref_implies_governing_relation` | Derived incarnation/domain relation |
| `acquire_ref_implies_live_domain` | Matching domain is live, without replacing evidence |
| `acquire_ref_rejects_missing_stability_evidence` | Absent ordinary evidence rejects |
| `acquire_ref_rejects_missing_access_or_provenance_premise` | Absent omitted-access premise rejects |
| `acquire_ref_rejects_wrong_domain` | Wrong domain rejects |
| `acquire_ref_rejects_incarnation_mismatch` | Wrong exact incarnation rejects |
| `ended_incarnation_cannot_acquire_ref` | Any ended token identity rejects |
| `initialize_yields_current_ptr` | Successful initialize's result identity is fresh and current |
| `initialize_ptr_can_acquire_ref` | Result ptr accepts with caller premises |
| `reinitialize_does_not_revive_old_ptr` | Recorded old identity rejects at reinitialized live site |
| `stale_ptr_after_take_cannot_acquire_ref` | F0.4 take-end connection |
| `stale_ptr_after_destroy_cannot_acquire_ref` | F0.4 destroy-end connection |
| `take_then_reinitialize_does_not_revive_old_ptr` | Take retains old identity for freshness rejection |
| `destroy_then_reinitialize_does_not_revive_old_ptr` | Destroy retains old identity for freshness rejection |
| `ptr_remains_live_across_current_value_replace` | Lifetime-preserving value change allows acquisition with new-state caller obligations |

Concrete declarations in `NewLang.F0.Counterexample.Reference` (10):

- `initialized_ptr_is_safely_issued_and_acquires_ref`
- `take_stale_ptr_contrast`
- `destroy_stale_ptr_contrast`
- `same_site_reinitialize_old_ptr_rejected_new_ptr_accepted`
- `same_site_destroy_reinitialize_old_ptr_rejected_new_ptr_accepted`
- `missing_stability_wrong_domain_and_missing_access_are_rejected`
- `replace_changes_current_fact_but_same_ptr_acquires_ref`
- `omitting_only_incarnation_freshness_revives_stale_ptr`
- `omitting_incarnation_match_accepts_old_ptr_after_fresh_reinitialize`
- `omitting_domain_match_accepts_wrong_live_domain`

## Validation and findings

The complete checker retains all 180 previous declarations and adds these 28:
**208 audited theorem reports**. It scans owned Lean sources for proof placeholders
and custom declarations, and accepts only the standard logic dependencies
`propext`, `Classical.choice`, `Quot.sound` (or none). No custom semantic assumptions,
proof placeholders, or kernel bypass are introduced.

Final local validation uses:

```bash
lake clean newlang-formal
lake build
bash scripts/check-proofs.sh
```

The local clean build succeeds (623 jobs), and all 208 reports pass. Lean 4.34.1,
elan 4.2.4, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, all toolchain/
manifest/bootstrap pins and the existing CI workflow are unchanged.

Branch `f0.5-ptr-ref-acquisition` was reviewed and merged in PR #4. The
existing `Lean proofs` workflow checks the committed pin/manifest in fresh runner
paths. The historical PR records its final **pull_request-event current-head** CI
URL/status. F0.6 retains that workflow and follows the dedicated-branch/open-PR
flow; CI success does not authorize automatic merge.

- **FORMAL-ENCODING:** External location/incarnation token, source issuance versus
  arbitrary Lean construction, evidence domain versus evidence possession, omitted
  access/provenance abstraction. State and WellFormed unchanged.
- **FORMAL-LEMMA:** Acquisition → exact live incarnation/governing domain; retained
  token stale rejection, same-site non-revival and current-value/lifetime distinction.
  Omitted-guard countermodels isolate three necessary rules.
- **FORMAL-SCOPE:** The following excluded properties remain unproved.
- No new **FORMAL-HOLE**, **FORMAL-AMBIGUITY**, or **FORMAL-EXTRACTION** was found
  in the inspected source rules. The resolved original milestone extraction history
  remains in the notes. No normative text is changed.

F0.5 does **not** establish whole-language memory/type safety; all pointer provenance,
BackingRegion liveness, alignment/range or allocation/deallocation safety; actual
block-scoped ref non-escape, return/capture or transitive scope dependency rules;
exclusive ref/alias algebra; concurrency safety; domain finalization safety;
structural/conditional subobject occurrence safety; FFI/raw pointer safety; or
compiler correctness. No ref shortening, NLL, read/write mutation semantics,
pointer arithmetic/conversion/addr operation, general reference/ownership framework,
or F0.6 transition is introduced.

F0.5 was reviewed and merged in PR #4 at main
`47baa1885dc17263cacb6bf6623568644589101f`. This report records the F0.5-stage
model and its 208 audits. F0.6 now extends State/WellFormed with domain carrier
coherence while retaining those theorem statements and audits; see the
[F0.6 report](F0_6_DOMAIN_TRANSFER_FINALIZATION_REPORT.md). The acquisition
observation kernel is reused without adding future-use ref scope semantics.
