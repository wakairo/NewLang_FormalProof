# F0.4 — lifetime / occupancy report

F0.4 starts and ends root lifetimes, while preserving the typed occupancy responsibility and historical identity allocation. It implements Draft 17.4 §14 and F0 bridge §17–19. The verified baseline is merged main `87fa293`, with all 102 F0.0–F0.3 audited proofs passing before changes.

| Operation | Occupancy | Old value | Root relation / identity |
| --- | --- | --- | --- |
| initialize | Vacant → live | Incoming loose → installed | Fresh incarnation/current fact; governing supplied live D |
| take | Live → Vacant | Survives as loose result | Incarnation/current fact/governing relation ended; D remains live |
| destroy | Live → Vacant | No surviving carrier; requires Discardable | Same root end, with atomic discard; D remains live |

## Ghost history and regression boundary

State adds `usedIncarnations : Finset IncarnationId`. `FreshIncarnation s i` means `i ∉ s.usedIncarnations`; `IncarnationsRecorded` is the new WellFormed component requiring every live incarnation to be recorded. `LiveIncarnation` derives liveness from occupancy and is not mutable state. `State.empty` has empty incarnation history.

Initialize inserts the new incarnation and current fact, retaining both old histories. Take/destroy preserve both histories exactly; dead identities never become eligible for reuse. Initial states must seed all earlier allocations, as with usedValueFacts. These sets are proof-only ghost state and do not require runtime/compiler history storage.

Replace, store and both swap cases preserve usedIncarnations exactly. Existing fixture constructors seed live identities; their new WellFormed field is reproved. All earlier public theorem statements are preserved, without weakening semantic claims. The extension is FORMAL-ENCODING, not a semantic revision of previous operations.

Lean 4.34.1, elan 4.2.4, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, toolchain/manifest pins, bootstrap and CI workflow are unchanged. Draft 17.4 is unchanged. Older milestone reports describe their historical scopes; this report records the F0.4 extension.

## Site/place decision and source API abstraction

`RootSiteLayout` is an injective `RootLocationId → PlaceId` association held fixed in the proof context of an execution. Initialize's root place is **sites.placeAt location**, not an arbitrary supplied or newly allocated PlaceId. The same location and layout yield the same place during reinitialization. Nominal ID types remain separate; the fixture's index-preserving association is an encoding, not normative equality or a compiler representation. No global layout-coherence invariant is imposed on older states; their places are unchanged. An execution of initialize uses one fixed layout rather than changing that context between calls.

Draft 17.4 §14.1–2 conserves the same typed occupancy site/range, while F0 §4.2 permits a location/place correspondence as a proof encoding. The documents do not mandate a unique implementation of that correspondence. This can be resolved as FORMAL-ENCODING without changing a semantic rule.

Source operations consume/return slot claims and use ptr/ref. F0.4 abstracts them with RootLocationId, Vacant/live root occupancy, package carriers and DomainId. Vacant is the site's empty occupancy responsibility. **Root-only requirement is structurally satisfied by F0 scope:** every live occupancy is a lifetime root. No explicit slot value carrier, PtrToken/ref acquisition, aggregate/subobject lifetime tree, BackingRegion/range geometry, Storage, or allocation is introduced.

## Transition legality and authorization

`initializeCandidate` installs a loose incoming package at a vacant site, builds a root with fresh incarnation/current fact and the supplied governing domain, removes the incoming loose carrier and inserts both new IDs. Other locations, package table and live domains are unchanged. `RawInitialize` requires vacancy, incoming looseness, live supplied domain, both freshness properties, ordinary `CanInitialize` authorization and type agreement. It requires neither Discardable nor exclusive/lifetime-ending authority. Governing domain is not inferred from package data or dependencies.

`takeCandidate` clears the root and inserts the old package as a loose carrier. `destroyCandidate` clears the root and erases the old carrier; inactive package-table records may remain. Both preserve other locations, package data, live domains and histories. `RawTake` / `RawDestroy` require the live root, `endingDomain = root.governing`, and an abstract caller proposition `CanEndRoot`. Production does not fix it to True; True is used only in fixtures. The domain equality survives abstraction and wrong-domain/missing-authority cases reject even raw transitions.

Destroy additionally requires a defined old ValuePackage with `discardable = true`. **Destroy uses the existing proof-side abstraction; this is not a runtime package flag requirement.** Normative Discardable is type-level; no type-system framework or destructor/Drop protocol is added.

`InitializeStep`, `TakeStep`, `DestroyStep` each require WellFormed pre/raw/post. Preservation projects legal post-state well-formedness; carrier transfer/consumption, vacancy, frame, histories, identity end and rejection proofs supply separate substantive evidence. No theorem assumes every raw candidate is legal.

At the visible value level destroy resembles take plus discarding the old result. For dependency legality it is **one combined atomic transition**, never a legal TakeStep followed by discard. Ordinary post-state DependenciesValid rejects old self-dependency in take (old package survives), permits old-only dependency to disappear in destroy, and rejects third-survivor dependencies in either operation. Table presence is not semantic survival.

## Governing lifecycle and occupancy conservation

Governs derives `(incarnation, domain)` from a live root; its relation is not package-owned and no separate relation table is added. Initialize creates a relation to supplied D. Take/destroy end the incarnation and therefore every such root relation; package-table identity proves the relation is not copied into a result. DomainId D itself is never removed from liveDomains. A concrete non-discardable take result carries DomainLive(D) and remains legal after the root ends.

The lifecycle fixture starts vacant with a loose non-discardable package and live D. Initialize installs it with O1/VF1; take restores the same vacancy and the same package as a unique loose carrier. The intermediate carrier is also uniquely installed, proving no lost/duplicated package responsibility. Function-based exclusive occupancy represents the one site responsibility; the theorem does not claim to implement source slot affine typing.

Reinitialize at the same location/layout creates O2/VF2, with O2 ≠ O1, VF2 ≠ VF1, both new IDs fresh beforehand and both old IDs still recorded. Place remains the same. The old incarnation is dead yet cannot be reused by RawInitialize; neither can the old current fact. Final state need not equal initial state because allocation history remains.

## Concrete witnesses and break-tests

- Independent initialize/take/destroy have legal witnesses. Initialize and take accept non-discardable values; destroy rejects them.
- The same discardable old self-dependent pre-state rejects every take candidate but admits destroy.
- A third loose package carrying the ended current fact rejects both take and destroy.
- A raw self-dependent take and a raw third-dependent destroy each satisfy all seven non-dependency invariant fields, including IncarnationsRecorded, but fail DependenciesValid alone.
- Omitting just destroy discardability permits loss of a non-discardable carrier despite well-formed pre/post states; the normal raw relation rejects it. The omitted-guard predicate stays private in the counterexample module.
- Wrong ending domains and False ending authority reject both raw end operations. Dead supplied domains and False initialization authority reject RawInitialize.

## Machine-checked inventory

The checker audits 180 reports: all 102 earlier declarations plus 78 new declarations (four prior-operation history helpers, 54 lifetime kernel/helper proofs, 20 lifetime fixtures).

Prior-operation additions (`NewLang.F0`):

- `replace_preserves_incarnation_history`
- `store_preserves_incarnation_history`
- `swap_same_preserves_incarnation_history`
- `swap_distinct_preserves_incarnation_history`

Lifetime production declarations (`NewLang.F0`):

| Theorem | Checked property |
| --- | --- |
| `RawInitialize.target_after` | Exact target root |
| `initialize_preserves_wellFormed` | Legal post-state invariant |
| `initialize_consumes_vacancy` | Vacant pre, live post |
| `initialize_installs_package` | Incoming installed and not loose |
| `initialize_package_unique_installed_carrier` | No duplicated incoming carrier |
| `initialize_incarnation_history_monotone` | Retain all prior incarnation allocations |
| `initialize_value_fact_history_monotone` | Retain all prior value-fact allocations |
| `initialize_creates_fresh_incarnation` | Fresh, recorded and live new incarnation |
| `initialize_creates_fresh_current_fact` | Fresh, recorded and current new value fact |
| `initialize_creates_governing_relation` | Supplied D governs the new incarnation |
| `initialize_uses_stable_site_place` | Place obtained from fixed site layout |
| `initialize_preserves_other_locations` | Occupancy frame |
| `initialize_preserves_package_data` | Table/dependencies unchanged |
| `initialize_preserves_live_domains` | Live domains unchanged |
| `initialize_rejects_reused_incarnation` | Historical incarnation reuse rejects |
| `initialize_rejects_reused_current_fact` | Historical fact reuse rejects |
| `initialize_rejects_dead_domain` | Dead supplied D rejects |
| `initialize_rejects_missing_authority` | Absent ordinary authority rejects |
| `take_preserves_wellFormed` | Legal post invariant |
| `take_restores_vacancy` | Target vacant |
| `take_preserves_other_locations` | Occupancy frame |
| `take_preserves_package_data` | Table/dependencies unchanged |
| `take_preserves_live_domains` | Domain identities remain live |
| `take_preserves_identity_histories` | Both histories unchanged |
| `take_ended_identities_remain_recorded` | Ended incarnation/fact remain allocated |
| `take_ends_incarnation` | Old incarnation no longer live |
| `take_old_current_fact_not_live` | Exact old fact dead |
| `take_ends_governing_relation` | All old-incarnation governing relations end |
| `take_does_not_finalize_domain` | DomainLive(D) preserved |
| `take_rejects_wrong_ending_domain` | Wrong authority-domain identity rejects |
| `take_rejects_missing_authority` | Missing end authority rejects |
| `destroy_preserves_wellFormed` | Legal post invariant |
| `destroy_restores_vacancy` | Target vacant |
| `destroy_preserves_other_locations` | Occupancy frame |
| `destroy_preserves_package_data` | Table/dependencies unchanged |
| `destroy_preserves_live_domains` | Domain identities remain live |
| `destroy_preserves_identity_histories` | Both histories unchanged |
| `destroy_ended_identities_remain_recorded` | Ended incarnation/fact remain allocated |
| `destroy_ends_incarnation` | Old incarnation no longer live |
| `destroy_old_current_fact_not_live` | Exact old fact dead |
| `destroy_ends_governing_relation` | All old-incarnation governing relations end |
| `destroy_does_not_finalize_domain` | DomainLive(D) preserved |
| `destroy_rejects_wrong_ending_domain` | Wrong authority-domain identity rejects |
| `destroy_rejects_missing_authority` | Missing end authority rejects |
| `take_old_package_survives_as_loose` | Loose old result survives |
| `take_old_package_unique_loose_carrier` | Only one result carrier |
| `take_survivors_preserved` | All prior survivors remain tracked |
| `take_rejects_surviving_old_current_dependency` | Any survivor carrying ended fact rejects |
| `take_rejects_old_self_current_dependency` | Old self-dependent result rejects |
| `destroy_old_package_does_not_survive` | Every old carrier consumed |
| `destroy_other_survivors_preserved` | All other survivors remain tracked |
| `destroy_rejects_other_surviving_old_current_dependency` | Third surviving dependency rejects |
| `destroy_requires_discardable_old_package` | Static applicability premise retained |
| `destroy_rejects_nondiscardable_old_package` | Non-discardable old value rejects RawDestroy |

Concrete declarations (`NewLang.F0.Counterexample.Lifetime`):

- `before_wellFormed`
- `independent_take_is_legal`
- `take_accepts_nondiscardable_value`
- `take_preserves_domain_live_dependency`
- `independent_destroy_is_legal`
- `destroy_can_eliminate_old_only_dependency`
- `old_self_dependency_rejects_take_but_allows_destroy`
- `third_survivor_rejects_take`
- `third_survivor_rejects_destroy`
- `nondiscardable_destroy_is_rejected`
- `unchecked_destroy_without_discardability_loses_nondiscardable_package`
- `unchecked_take_breaks_dependencies`
- `unchecked_destroy_third_dependency_breaks_candidate`
- `initialize_accepts_nondiscardable_value`
- `initialize_then_take_conserves_occupancy_responsibility`
- `reinitialize_same_location_uses_fresh_incarnation`
- `dead_historical_incarnation_cannot_be_reused`
- `historical_value_fact_reuse_is_rejected`
- `wrong_domain_and_missing_authority_are_rejected`
- `dead_domain_and_missing_initialize_authority_are_rejected`

## Validation, findings and next milestone

Local validation uses a clean project rebuild and the complete audit:

```bash
lake clean newlang-formal
lake build
bash scripts/check-proofs.sh
```

The proof checker scans all project-owned Lean source for placeholders/custom declarations and audits the 180 theorem dependency reports. Only standard propext, Classical.choice and Quot.sound are allowed. No semantic shortcuts or custom semantic assumptions are introduced.

The existing Lean proofs workflow bootstraps pinned tools/manifest in fresh temporary paths. Work uses branch `f0.4-lifetime-occupancy`, an open main-targeting PR, and confirmation of the pull_request-event run for its current head. The PR records the final current-head CI URL/result; green CI does not merge the PR.

- **FORMAL-ENCODING:** Incarnation ghost history, derived LiveIncarnation/Governs, Vacant occupancy abstraction and fixed site/place association.
- **FORMAL-LEMMA:** Survivor distinction, unique carrier round-trip, fresh same-site reinitialization, and root relation end versus domain survival.
- **FORMAL-SCOPE:** Flat root-only state; ptr/ref deferred to F0.5, domain finalization to F0.6, backing geometry/structural descendants excluded. No generic transition/lifetime/ownership framework was introduced.
- No new **FORMAL-HOLE**, **FORMAL-AMBIGUITY**, or **FORMAL-EXTRACTION** issue was found in the inspected rules. Site/place association is a permitted proof encoding; the resolved milestone-number history remains in the notes. Draft 17.4 is unchanged.

After semantic/formalization review and merge, F0.5 can use LiveIncarnation, retained ended IDs and distinct reinitialization identities to prove persistent pointer incarnation safety. No PtrToken/ref acquisition is implemented here; whole-language soundness remains outside the established claims.
