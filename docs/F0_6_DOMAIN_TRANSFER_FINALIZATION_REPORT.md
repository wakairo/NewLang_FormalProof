# F0.6 — LifetimeDomain transfer / finalization

## Goal and normative boundary

F0.0–F0.5 were reviewed and merged in main
`47baa1885dc17263cacb6bf6623568644589101f` (F0.5 PR #4).
Before any change, `lake build` and `bash scripts/check-proofs.sh` passed:
623 build jobs, all 208 audited declarations. F0.6 was submitted on `f0.6-domain-transfer-finalization` and subsequently
reviewed/merged in PR #5 at main `92c9ed7610fb3f1c419788194f83979a63172731`.
The human review closed the limited F0 flat semantic kernel. This report retains
the F0.6-stage claims and audit history.

Draft 17.4 §13.1–3 / §14.5–6 are the normative inputs. The F0 bridge §20.2–3 is
non-normative. Lean is proof encoding. **Formal representation choices are
non-normative.** Draft 17.4 is unchanged; the resolved original milestone-number
FORMAL-EXTRACTION history is retained.

The central distinction is:

| Operation | Domain identity | Value carrier | Governed root / DomainLive survivor |
| --- | --- | --- | --- |
| Transfer | Same D stays live | D's abstract owner changes | Preserved; these do not block transfer |
| Finalization | D ends | D's ownership entry is consumed | Must not be stranded; either blocks legal end |

## State and WellFormed extension

`DomainValueCarrierId` is a nominal structure wrapping Nat, separate from the six
core identity types. It identifies an abstract semantic owner, not a machine
address, PlaceId, RootLocationId, PackageId or IncarnationId. F0.6 does not model
the actual source/destination place or incarnation of a LifetimeDomain-typed
object and does not prescribe a runtime carrier map.

```
State.domainValueCarrier : DomainId → Option DomainValueCarrierId
DomainCarrierCoherent s :=
  ∀ D, D ∈ s.liveDomains ↔ ∃ c, s.domainValueCarrier D = some c
```

Option supplies a unique current owner per D. **Reverse injectivity is not a
requirement**: multiple live identities may share one abstract owner. A concrete
well-formed fixture demonstrates this. Ending D clears only its entry; another D
sharing that owner retains its entry. Carrier consumption is not physical deletion
of an owner object.

DomainCarrierCoherent is the ninth WellFormed component; the previous eight are
unchanged. Empty has no live domains or carriers. Replace/store/distinct swap and
initialize/take/destroy candidates copy the map; same swap is exact state identity.
Old fixtures seed all live domains with a carrier and prove coherence. Their
existing public theorem statements and all 208 audit entries are retained.
No old operation gains a new caller requirement. Seven new frame theorems make the
carrier preservation explicit, and two coherence projections connect liveness and
ownership.

## Exact transfer representation

```
domainTransferCandidate s D newCarrier =
  s with domainValueCarrier[D] := some newCarrier

RawDomainTransfer transferAllowed s D oldCarrier newCarrier post:
  D ∈ s.liveDomains
  s.domainValueCarrier D = some oldCarrier
  transferAllowed
  post = domainTransferCandidate s D newCarrier

DomainTransferStep = WellFormed pre ∧ RawDomainTransfer ∧ WellFormed post
```

The caller proves transferAllowed. It abstracts omitted source-current-value
capability conflicts and ordinary transfer applicability. An actual capability
referring to the LifetimeDomain object's current value can obstruct moving that
object; this is different from a dependency on DomainLive(D). These source-object
facts and lexical references are not encoded by the abstract carrier. The premise
is never defined as universally True in production. True is used only in concrete
controls to isolate modeled rules. A no-op carrier assignment is not forbidden;
the positive movement witness explicitly uses different old/new carrier IDs.

Only D's entry changes. The complete live-domain set, every occupancy/root place,
incarnation, current fact, package and governing domain, all package/dependency
data, loose carriers, both allocation histories, LiveFacts and survivors are
preserved. Other domain carrier entries are unchanged. A WellFormed pre and raw
transfer suffice to prove WellFormed post; legal preservation also projects its
recorded post invariant. Transfer creates no fresh domain or root identity.

Given AcquireRef in pre, legal transfer and **separate post-state caller
stability/access proofs**, the same ptr and evidence DomainId can acquire in post.
The production theorem permits different pre/post propositions and any evidence
domain; it uses occupancy preservation. This is point-of-acquisition preservation,
not a proof that an already acquired ref can remain in a lexical scope across a
source-level transfer. The fixture has both a governed root and actual surviving
DomainLive dependency and proves acquisition before and after moving D's carrier.

## Exact finalization representation

```
finalizeDomainCandidate s D =
  s with liveDomains := s.liveDomains.erase D,
         domainValueCarrier[D] := none

RawFinalizeDomain canFinalize s D carrier post:
  D ∈ s.liveDomains
  s.domainValueCarrier D = some carrier
  canFinalize
  post = finalizeDomainCandidate s D

FinalizeDomainStep = WellFormed pre ∧ RawFinalizeDomain ∧ WellFormed post
```

CanFinalize is a caller proof for omitted scoped-capability/applicability
conditions. Modeled root and package-dependency conflicts are **not** hidden in
this proposition or duplicated as raw guards. They follow from ordinary post
WellFormed. Production does not universally set the caller condition to True.

Finalization removes D and DomainLive(D) and clears D's carrier entry. It preserves
other identities and their entries, occupancy, packages, loose carriers, survivors
and both histories. There is no automatic root destruction, package consumption,
dependency rewriting or governing-domain retargeting.

The post-state DomainsValid implies there was no live root governed by D, because
occupancy is preserved. DependenciesValid implies no surviving pre package carried
DomainLive(D), because carriers and package data are preserved while that fact dies.
The corresponding rejection theorems apply to every candidate legal end, not just
one fixture. After a legal end, AcquireRef cannot use D. Raw live-domain/current-
carrier/caller guards reject dead domains, repeated end, mismatching carriers and
missing permission independently.

LifetimeDomain is non-Discardable in the normative language. Its abstract carrier
is not forced into ValuePackage's Bool field; no implicit discard transition for
this carrier exists. Only explicit finalization in the modeled operations consumes
D's ownership entry. General authority/Drop/destructor machinery is not introduced.

## Concrete controls and break-tests

All deliberate broken rules are private in Counterexample/Domain.lean. Production
Domain.lean contains only the intended candidates and relations.

| Control | Machine-checked result |
| --- | --- |
| Independent transfer | Legal transfer moves C0 to distinct C1 while D stays live |
| Governed root | Same pre: transfer legal and Governs preserved; every finalization rejects |
| DomainLive-dependent loose survivor | Same pre: transfer legal and dependency live; every finalization rejects |
| Independent finalization | Legal end removes D and its entry, retaining other D and shared C0 entry |
| Root plus dependent survivor | Transfer legal; same ptr/D acquires before and after with post premises |
| Destroy then finalization | End first rejects; legal destroy ends root but keeps D/carrier; later end legal |
| Shared carrier | Two distinct live domains in a WellFormed state share C0 |
| Missing permissions / wrong carriers | Both raw relations reject |
| Dead/repeated domain end | Raw transfer and raw finalization reject after D ends |

Three required break-tests isolate different responsibilities:

1. **TransferRenamingIdentity:** a private operation replaces D0 by D1 and moves its
   carrier entry. Both endpoints are WellFormed with no roots or dependencies.
   The real DomainTransferStep is impossible because D0 must remain live. Hence
   endpoint WellFormed alone does not enforce an operation's identity semantics.
2. **Unchecked root finalization:** WellFormed pre plus the real raw end produces a
   candidate with its governed root still present. CarrierUnique, PlacesUnique,
   IncarnationsUnique, PackagesPresent, DependenciesValid, ValueFactsRecorded,
   IncarnationsRecorded and DomainCarrierCoherent all hold; **only DomainsValid fails**.
3. **Unchecked dependency finalization:** no roots, but a loose survivor carries
   DomainLive(D). WellFormed pre plus the real raw end produces a candidate where
   all eight other fields hold, including DomainsValid and carrier coherence;
   **only DependenciesValid fails**.

These are omitted-legality countermodels, not contradictions of legal normative
operations. Finalization's preservation theorem is intentionally a post-invariant
projection; the candidate frames, derived no-stranding facts and isolated failures
supply substantive evidence.

## Audited theorem inventory

All names below are prefixed `NewLang.F0` unless the fixture namespace is stated.
The existing 208 audits remain. F0.6 adds 58 declarations: 9 coherence/frame,
18 transfer, 19 finalization and 12 concrete controls, for **266** total.

### Coherence and earlier-operation frames

- `initialize_preserves_domain_carriers`
- `take_preserves_domain_carriers`
- `destroy_preserves_domain_carriers`
- `replace_preserves_domain_carriers`
- `store_preserves_domain_carriers`
- `swap_same_preserves_domain_carriers`
- `swap_distinct_preserves_domain_carriers`
- `wellFormed_live_domain_has_value_carrier`
- `wellFormed_domain_carrier_implies_live_domain`

### Transfer

- `domain_transfer_preserves_wellFormed`
- `domain_transfer_preserves_identity`
- `domain_transfer_preserves_liveness`
- `domain_transfer_moves_value_carrier`
- `domain_transfer_preserves_other_carriers`
- `domain_transfer_preserves_roots`
- `domain_transfer_preserves_governing_relations`
- `domain_transfer_preserves_packages`
- `domain_transfer_preserves_histories`
- `domain_transfer_preserves_liveFacts`
- `domain_transfer_preserves_survivors`
- `domain_transfer_preserves_DomainLive_dependencies`
- `raw_domain_transfer_preserves_wellFormed`
- `domain_transfer_step_of_raw`
- `domain_transfer_preserves_acquire_ref`
- `domain_transfer_rejects_missing_permission`
- `domain_transfer_rejects_dead_domain`
- `domain_transfer_rejects_wrong_carrier`

### Finalization

- `finalize_domain_preserves_wellFormed`
- `finalize_domain_ends_identity`
- `finalize_domain_consumes_value_carrier`
- `finalize_domain_preserves_other_domains`
- `finalize_domain_liveDomains_subset`
- `finalize_domain_preserves_other_carriers`
- `finalize_domain_preserves_occupancy`
- `finalize_domain_preserves_packages`
- `finalize_domain_preserves_histories`
- `finalize_domain_preserves_survivors`
- `finalize_domain_preserves_carrier_coherence`
- `finalize_domain_requires_no_governed_roots`
- `finalize_domain_rejects_live_governed_root`
- `finalize_domain_requires_no_surviving_domain_dependency`
- `finalize_domain_rejects_surviving_domain_dependency`
- `finalize_domain_rejects_dead_domain`
- `finalize_domain_rejects_missing_permission`
- `finalize_domain_rejects_wrong_carrier`
- `finalized_domain_cannot_acquire_ref`

### Concrete controls — namespace NewLang.F0.Counterexample.Domain

- `simple_domain_transfer_is_legal`
- `governed_root_allows_transfer_but_rejects_finalization`
- `DomainLive_dependency_allows_transfer_but_rejects_finalization`
- `independent_domain_finalization_is_legal`
- `one_carrier_may_hold_multiple_domain_identities`
- `transfer_with_root_and_dependency_preserves_acquisition`
- `unchecked_finalization_strands_governed_root_only`
- `unchecked_finalization_strands_domain_dependency_only`
- `ending_root_allows_later_domain_finalization`
- `broken_identity_rename_can_preserve_wellFormed`
- `missing_permissions_and_wrong_carriers_are_rejected`
- `dead_domain_cannot_transfer_or_be_finalized_again`

## Validation and changed files

The baseline passed before changes. The extended project passes `lake build`
(625 jobs) and `bash scripts/check-proofs.sh` (266 reports). Final verification cleans only the root package and
reruns both checks on the committed branch before submission. The audit
scans all project-owned Lean sources for sorry/axiom/admit and checks each
`#print axioms` report. Only standard `propext`, `Classical.choice` and `Quot.sound`
are allowed; there are no custom semantic axioms or proof placeholders.

The existing push/pull_request Lean proofs workflow is unchanged. It bootstraps
pinned Lean/mathlib in empty runner-temporary directories and audits the complete
project. The PR records the actual pull_request-event run URL, final head SHA and
success status; it must be green at that exact head and remain open/unmerged.

Lean 4.34.1, elan 4.2.4, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, toolchain/manifest/bootstrap and CI
pins are unchanged. Draft 17.4 SHA-256 remains
`a552468ec3d96a79d17495fb251f63475c752ee0a8ee1e1ffa5bf9a887818c12`.

Changed files:

- New: `NewLang/F0/Domain.lean`, `NewLang/F0/Counterexample/Domain.lean`, this report.
- Model extension: `Id.lean`, `State.lean`, `WellFormed.lean`.
- Map frames: `Replace.lean`, `Store.lean`, `Swap.lean`, `Lifetime.lean`.
- Mechanical fixtures: `Counterexample/{Replace,Store,Swap,Lifetime,Reference}.lean`.
- Imports/audit: `NewLang.lean`, `scripts/check-proofs.sh`.
- Documentation: both READMEs, both FORMALIZATION_NOTES, the F0 bridge and the
  historical F0.5 report's reviewed/merged status.

## FORMAL findings and scope

| Classification | F0.6 finding |
| --- | --- |
| FORMAL-ENCODING | Nominal carrier/map/coherence, shared ownership and mechanical extension; source/runtime layout is not prescribed |
| FORMAL-LEMMA | Same-identity frames, no-stranding consequences, contrast/lifecycle/acquisition witnesses, isolated break-tests |
| FORMAL-SCOPE | Actual source domain-value/current-fact conflicts and lexical caps remain caller premises; creation, geometry and F1 are deferred |
| FORMAL-HOLE | None found in inspected rules |
| FORMAL-AMBIGUITY | None found in inspected rules |
| FORMAL-EXTRACTION | No new correction; resolved pre-F0.1 milestone history retained |

No domain-creation operation is added. Draft 17.4 §13.1 requires fresh identity on
creation; future creation/recreation must enforce it. Current transitions retain
or shrink the domain set, so usedDomainIds is unnecessary here. General authority
algebra, lexical scope/non-escape, BackingRegion, Storage/allocation authority,
aggregate/subplace/sum/span, functions/callbacks/generics, FFI, LLVM and concurrency
remain outside this milestone. Normative source semantics have not changed.

## M8 feedback

Carrier transfer should communicate continuity of the **same domain identity**;
it should not look like identity replacement. Finalization should communicate an
explicit identity-ending action, separate from ending governed roots. Diagnostics
should distinguish a still-governed live root from a surviving DomainLive semantic
dependency, and distinguish either from a source-current-value capability conflict
on transfer. A live domain identity alone does not prove possession of caller
stability evidence. The formal carrier map is not an API layout requirement;
this feedback fixes no source syntax or ABI.

## F0 closure assessment

| Area | Assessment | Boundary |
| --- | --- | --- |
| F0-T transition preservation | Covered in flat kernel; partially covered at language level | Legal pre/raw/post relations; static caller derivations remain abstract |
| Current-value dependency | Covered for modeled exact facts and tracked survivors | Scope/backing fact kinds, payload/authority algebra remain outside F0 |
| replace / store / swap | Covered | Survivor contrast, no retargeting, freshness and laundering rejection; full source typing outside |
| Lifetime start/end | Covered for flat roots | Fixed-site start, fresh incarnation, take/destroy survivor contrast; actual slot/backing geometry outside |
| Persistent ptr stale safety | Partially covered | Exact point acquisition and non-revival after fresh start; provenance/access and lexical future-use scopes outside |
| Domain transfer/finalization | Covered in abstract carrier subset | Same identity versus end, modeled no-stranding and explicit omitted caller obligations; creation/source object geometry outside |
| Counterexample policy | Covered for implemented kernel | Private omitted-rule controls, positive witnesses, axiom audit and pinned CI; not exhaustive whole-spec testing |
| Whole-language/parser/compiler correctness | Outside F0 | No such safety/correctness claim |
| Lexical refs/functions/callbacks/recursion | Outside F0 | Non-escape, scope propagation and function-boundary analysis unproved |
| BackingRegion/Storage/Allocation authority | Outside F0 | Alignment/range/provenance and allocation geometry unproved |
| Aggregates/subobjects/sums/spans, opaque relocation, FFI, concurrency | Outside F0 | No implementation or theorem claim |

The implemented F0.0–F0.6 **flat semantic kernel** was reviewed and CLOSED at
main `92c9ed7610fb3f1c419788194f83979a63172731`. Closure is limited to this
abstract flat subset and does not establish whole-NewLang or compiler correctness.
The next reviewed track is F1; [F1.0's report](F1_0_STRUCTURAL_REFINEMENT_REPORT.md)
records its structural state/invariant scaffold while retaining the closed F0 semantics.
