# F1.0 — Structural Refinement Scaffold

## Scope and closed F0 baseline

F0.0–F0.6 were reviewed and merged; the **F0 flat semantic kernel is CLOSED** at
main `92c9ed7610fb3f1c419788194f83979a63172731` (F0.6 PR #5). Before edits,
`lake clean newlang-formal`, `lake build` (625 jobs), and
`bash scripts/check-proofs.sh` (266 reports) all passed. F1.0 retains every audit
and leaves every `NewLang/F0/*.lean` source and theorem statement unchanged.

Work is on `f1.0-structural-refinement-scaffold`, targeting main through an open,
unmerged PR. F1.0 supplies state/invariant refinement only: no F1 Step, fixed-field
or whole-aggregate operation, sum/OccurrenceId, BackingRegion/ByteRange,
Storage/slot refinement, relocation, lexical ref scope, function boundary or source
syntax is implemented. F1.1 is a later reviewed milestone.

Draft 17.4 remains normative, the F0 bridge remains non-normative, and Lean is proof
encoding. Required inputs inspected include §3.5–6, §13.5a canonical structural
state/ownership, §17.4 fixed aggregate behavior, §26 conditional occurrence and
§24.4 fresh destination structural identity. Future sections guide extension points;
their operations are not implemented. **Formal representation choices are
non-normative.** The normative document and closed F0 semantics are unchanged.

## Exact structural encoding

Reuse F0's nominal PlaceId, IncarnationId, ValueFactId, PackageId, DomainId and
RootLocationId. No duplicate identity namespace or new structural/occurrence/backing
ID is needed. A StructuralLayout contains:

```
places : Finset PlaceId
root   : PlaceId
path   : PlaceId → List Nat
```

Paths are root-relative semantic coordinates, not source field labels, array syntax,
byte offsets, padding, ABI layout, backing ranges or machine addresses. PlaceId
remains the stable semantic identity; the path gives its structural relationship.
Only the finite tracked support matters; map entries outside it are inactive data.

TreeWellFormed requires root membership, root path = [], injective paths on tracked
places and an immediate-prefix tracked parent for every non-root. Parent(l,p,q)
means both places are tracked and `path(q) = path(p) ++ [label]`. Ancestor is a
strict nonempty path-prefix relation; Descendant reverses its arguments. Below is
self-or-ancestor. StructuralRole is root at l.root and fixedSubobject elsewhere,
restricted to tracked nodes when interpreting liveness. Root has no parent, and
path length strictly increases down every parent/ancestor edge; cycles are
unrepresentable. Injectivity makes the empty-path root and each parent unique.

Siblings are distinct nodes with a shared immediate parent. Their paths have equal
length, so neither is the other's ancestor. StructuralOverlap is equality or
ancestor in either direction; KnownDisjoint is its negation. These are semantic
structural relations, not physical range proofs or a general pointer/heap graph.

## One canonical current-state and root lifetime

StructuralNodeState contains exactly incarnation, currentFact and localDeps.
StructuredRoot contains its layout, one `PlaceId → StructuralNodeState` mapping,
and root-only package ID, governing DomainId and discardability abstraction.
There is no stored duplicate F0 root or parent copy of a child's complete value.
Payload contents are deliberately opaque.

F1 State contains finite liveRoots, the canonical root map, loosePackages,
looseValues, liveDomains, domainValueCarrier, usedValueFacts and usedIncarnations.
There is no per-child occupancy or governing-domain field. Every tracked child is
live with its enclosing live root; independent child lifetime end is not an F1.0
operation. Root classification is available for later root-only applicability.
Loose values remain flat packages at this stage; stored table data with no loose
carrier is inactive. Installed root package data is derived from canonical nodes,
not read from that loose table.

All simultaneously live structural incarnations and current fact IDs are globally
unique across root locations and places. Incarnation and value fact remain distinct
nominal sorts even when fixtures use the same numeric index. Every tracked identity
belongs to the existing proof-only histories. Erasure retains all history, including
child identities whose liveness detail is erased. The concrete history control
proves a recorded child identity cannot become F0 FreshValueFact. No allocator,
identity supply, domain creation or F1 transition is introduced.

## Dependency ownership and liveness

```
LocalDeps(r,p) = (r.node p).localDeps
SubtreeDeps(r,p) = union LocalDeps(r,q)
                  for q ∈ r.layout.places with Below(r.layout,p,q)
```

SubtreeDeps is a derived filtered Finset.biUnion, never a second mutable summary.
A root's local dependencies can be empty while its complete subtree carries a
child's dependency. Local inclusion and child-to-parent subtree inclusion are
proved. Every subtree atom has a local owner in that subtree. In particular, an
atom visible at sibling b must come from b's own subtree, not from sibling a.
Disjointness does not forbid independently owning the same atom on both sides.

StructuralLiveFacts uses the existing Fact constructors. A value fact is live iff
its exact PlaceId/currentFact pair occurs in a tracked node of a live root; a
DomainLive atom is live iff the domain is live. Historical IDs do not establish
current liveness. F1 validates both node-local and surviving loose dependencies
against this precise view before any abstraction.

## F1 WellFormed inventory

Thirteen F1-side fields, without an embedded F0 WellFormed premise:

| Field | Requirement |
| --- | --- |
| trees | TreeWellFormed for every live root |
| placesUnique | A tracked PlaceId belongs to one live root location |
| incarnationsUnique | Equal live incarnation implies same location/place |
| currentFactsUnique | Equal live current-fact ID implies same location/place |
| installedUnique | Each installed package has one root carrier |
| installedNotLoose | Installed package is not also loose |
| loosePresent | Each loose carrier has package data |
| domainsValid | Each live root's governing domain is live |
| localDependenciesValid | All tracked node-local dependencies are precise live facts |
| looseDependenciesValid | All surviving loose dependencies are precise live facts |
| valueFactsRecorded | All current structural facts are recorded |
| incarnationsRecorded | All structural incarnations are recorded |
| domainCarrierCoherent | Same live-domain/current-carrier equivalence as F0 |

Exactly one root structural node, parent consistency and no cycles are structural
consequences of the tree fields. Root fact/incarnation/domain correspondence is
by erasure construction, not synchronization of two stored states. Subtree dependency
consistency is by definition. These cover the requested F1-WF1 through F1-WF9.

## Erasure and dependency strategies

Strategy A is adopted: an **exact currently live** structural value fact widens to
its enclosing root's current fact. Root facts anchor directly to their own canonical
node. Domain facts preserve identity. Unknown/stale value facts are retained rather
than silently remapped to a live fact. Classical selection locates the owner of a
live exact fact; global place ownership ensures that choice is unambiguous in
well-formed states. This uses standard Lean logic, not a semantic axiom or runtime
lookup requirement.

Strategy B would abstract at the coarse root-package summary boundary. Our derived
summary combines that boundary with per-atom strategy A, without storing a second
mutable summary. Strategy C (adding child roots to F0 or a different fact language)
is unnecessary and would blur the closed flat-kernel boundary. Exact child facts
cannot simply survive unchanged in F0: there is no F0 child occupancy to keep them
live. Dropping them would lose obligations.

```
eraseRoot(r) = LiveRoot(
  r.layout.root, r.node(root).incarnation, r.node(root).currentFact,
  r.package, r.governing)

eraseToF0(s).occupancy(l) = live eraseRoot(s.root l) if l ∈ liveRoots
                          vacant otherwise
installed package dependencies = image eraseFact(s) (SubtreeDeps(r,root))
loose package dependencies     = image eraseFact(s) original dependencies
```

Installed summaries use a finite union over owner locations; installedUnique proves
there is exactly one owner. `erase_root_package_exact` proves the actual table entry
has precisely that root's image dependency set and unchanged discardability. Loose
carrier IDs, domains/carrier map and both histories are retained exactly. Child-only
nodes/facts/incarnation liveness are erased; their allocated IDs are not erased from
history. Vacant means no live root at that location, without importing physical slot
or backing geometry.

Every source subtree obligation's image belongs to the computed installed summary.
`erase_local_dependency_obligation` additionally proves it belongs to the **actual
erased package table entry**. `erase_live_fact` proves a precise live fact's image is
live in F0. Together these establish dependency conservation and F0 validity.
Erasure is an abstraction, not exact identity preservation for child atoms; coarse
images may merge different obligations and lose sibling precision. No exact
one-to-one transition simulation or F0 raw replace correspondence is claimed.

## Central theorem and concrete validation

`f1_wellFormed_erases_to_f0_wellFormed` proves
`F1.WellFormed s → F0.WellFormed (eraseToF0 s)`. It assembles nine separate F0
invariant proofs derived from F1-side conditions: carriers, places, incarnations,
package presence, domains, dependencies, both histories and domain carrier coherence.
It is not a projection of an assumed erased WellFormed state.

The Pair/Holder fixture has one live root and two fixed children, distinct
incarnation/current fact IDs, empty root/count local dependencies and one dependency
owned only by the borrowed child. That atom is visible from child/root subtrees and
absent from the count subtree; no parent duplicate is needed. Its exact child fact
widens to the root current fact and remains in the actual erased root package.
Both F1 and erased F0 WellFormed are proved. The nested fixture adds a grandchild;
root and left are ancestors, right is not, and siblings remain disjoint. Overlap
controls check self, root/child in both directions and sibling non-overlap.

| Private break-test | Checked failure mode |
| --- | --- |
| Two-edge cyclic parent graph | Exists as a malformed graph but no semantic path layout can realize it; strict length would contradict itself |
| Duplicate parent | A concrete malformed layout gives left/right the same path and both parent a grandchild; TreeWellFormed rejects it. Duplicate parents are not representable in a well-formed layout |
| Root/child fact collision | WellFormed.currentFactsUnique rejects the same current ID at two nodes |
| Incarnation collision | WellFormed.incarnationsUnique rejects the same live incarnation at two nodes |
| Stale local dependency | Fact 99 is recorded but absent although child current fact is 1; history does not supply liveness and local dependency validity rejects |
| Broken dependency erasure | Both precise source and broken flat endpoint are WellFormed, but the child obligation disappears from the flat package; conservation, not F0 WellFormed alone, rules it out |

Collision/stale examples change only the relevant node fragments and contain no
transitions. Deliberately broken definitions are private and confined to
Counterexample/Structural.lean. Production erasure retains the obligation.

## Audited theorem inventory

The 266 closed-F0 audits are retained. All 66 new public F1 declarations below are
audited, giving **332 reports**. Production names use NewLang.F1; concrete names
use NewLang.F1.Counterexample.Structural.

### Structural (14)

- `parent_increases_depth`
- `structural_root_has_no_parent`
- `structural_nonroot_has_parent`
- `parent_unique`
- `parent_implies_ancestor`
- `ancestor_increases_depth`
- `ancestor_irreflexive`
- `ancestor_transitive`
- `below_transitive`
- `siblings_are_not_ancestors`
- `known_disjoint_siblings_do_not_overlap`
- `ancestor_implies_overlap`
- `same_place_implies_overlap`
- `root_contains_every_place`

### State (5)

- `local_deps_subset_subtree_deps`
- `ancestor_subtree_deps_subset`
- `child_subtree_deps_subset_parent_subtree_deps`
- `subtree_dependency_has_local_owner`
- `disjoint_sibling_dependency_not_owned_by_other_sibling`

### WellFormed (7)

- `live_structural_node_has_current_fact`
- `structural_current_fact_is_recorded`
- `distinct_live_nodes_have_distinct_current_fact_ids`
- `live_structural_node_has_incarnation`
- `structural_incarnation_is_recorded`
- `distinct_live_nodes_have_distinct_incarnations`
- `subtree_dependencies_live`

### Erasure (24)

- `erase_occupancy_live_iff`
- `erase_root_fact_matches_f0`
- `erase_root_incarnation_matches_f0`
- `erase_preserves_root_governing_domain`
- `erase_preserves_live_domains`
- `erase_preserves_domain_carriers`
- `erase_preserves_histories`
- `erase_live_fact`
- `erase_structural_value_fact_to_root`
- `erase_dependencies_are_conservative`
- `erase_installed_package_present`
- `installed_owner_is_unique`
- `erase_root_package_exact`
- `erase_local_dependency_obligation`
- `erase_carrier_unique`
- `erase_places_unique`
- `erase_incarnations_unique`
- `erase_packages_present`
- `erase_domains_valid`
- `erase_dependencies_valid`
- `erase_value_facts_recorded`
- `erase_incarnations_recorded`
- `erase_domain_carrier_coherent`
- `f1_wellFormed_erases_to_f0_wellFormed`

### Counterexample/Structural (16)

- `simple_pair_is_wellFormed`
- `simple_pair_erases_to_wellFormed_f0`
- `nested_structure_is_wellFormed`
- `pair_overlap_and_disjointness`
- `nested_ancestor_witness`
- `local_dependency_is_visible_from_root_subtree`
- `structural_dependency_is_retained_by_erasure`
- `child_histories_survive_flat_erasure`
- `cyclic_structure_is_rejected`
- `duplicate_parent_is_rejected`
- `concrete_duplicate_parent_is_rejected`
- `duplicate_root_child_fact_is_rejected`
- `duplicate_structural_incarnation_is_rejected`
- `stale_structural_dependency_is_rejected`
- `recorded_stale_fact_is_not_live`
- `broken_erasure_loses_child_dependency_obligation`

## Environment, verification and changed files

Lean 4.34.1, elan 4.2.4, mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, toolchain/manifest/archive checksums
and CI workflow are unchanged. Bootstrap's cache import changes from Finset.Basic
to Finset.Union, which includes Basic; with Set.Basic the closure grows from 591 to
655 cached modules at the same revision. No dependency upgrade or lockfile update.

`lake build` passes (694 jobs); `bash scripts/check-proofs.sh` passes all 332 reports.
Final verification cleans the root package and repeats both on the committed branch.
The source scan contains no sorry/axiom/admit shortcut. Axiom reports allow only
`propext`, `Classical.choice`, `Quot.sound` or no axioms. PR-triggered Lean proofs must
be green at the actual current head; the PR records the exact run URL/SHA/status
and remains open/unmerged. The existing CI bootstraps fresh pinned toolchain/cache
paths and checks the complete project.

New files: F1/Structural.lean, State.lean, WellFormed.lean, Erasure.lean,
Counterexample/Structural.lean and this report. Updated: NewLang.lean, both READMEs,
both FORMALIZATION_NOTES, the historical F0.6 report's closure status,
scripts/check-proofs.sh and scripts/bootstrap.sh. No F0 Lean or normative file changed.

## FORMAL findings

| Classification | Finding |
| --- | --- |
| FORMAL-ENCODING | Reused nominal PlaceId plus finite semantic paths; canonical fragments/derived union; finite root support and conservative strategy-A erasure |
| FORMAL-LEMMA | Parent/ancestor/overlap, global identity/history conditions, local ownership conservation and nine separately derived F0 invariants |
| FORMAL-SCOPE | State refinement only; loose values remain flat; exact Step simulation, operations, occurrence, backing and source API are deferred |
| FORMAL-HOLE | None found in inspected rules |
| FORMAL-AMBIGUITY | None found in inspected rules |
| FORMAL-EXTRACTION | No new correction; original resolved F0 milestone history retained |

## F1.1 handoff and later extension points

After semantic review, F1.1 can use Below/Ancestor and KnownDisjoint to freshen a
changed child's and ancestors' current facts while retaining disjoint sibling facts
and all fixed incarnations. Local ownership and subtree conservation support
survivor analysis. No such operation/theorem is implemented here. F0 erasure remains
a state sanity check; coarse dependency widening can lose precision, so future
Step-refinement claims need separate review and cannot assume literal F0 mutation.

F1.2 can enrich StructuralRole with conditional occurrence classification/identity
and active-node liveness. Paths give structural position, not occurrence identity;
no OccurrenceId is present. F1.3 can attach placement to the root and derive child
placement from the structural relation; there is no independent child physical
placement state to synchronize. F1.5 can construct a destination layout with new
PlaceIds and fresh node identities, preserving full histories; it must not transfer
source place-owned identities with the semantic package. This report fixes no API
syntax, type AST, physical layout or general graph framework.

F1.0 is ready for review of this limited structural scaffold. F1.1 may start after
review/adjudication. This task stops with an open PR and current-head green CI; it
does not merge, implement F1.1 or claim whole-language/compiler correctness.
