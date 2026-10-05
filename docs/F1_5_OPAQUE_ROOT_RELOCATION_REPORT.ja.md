# F1.5 — opaque lifetime-root relocation

Track: F

## Authority / baseline / review境界

[Issue #16](https://github.com/wakairo/NewLang_FormalProof/issues/16)に基づく**F1.5のみ**の証拠です。最初にCompiler mainの`docs/NewLang_Project_Development_Process.md`を読みました。change historyの正はGitです。本文は独立Version historyを持ちません。

- Compiler current main: `acac894fc6c50101a3995a8f930a070987529335`。
- `docs/reference/CURRENT_SPEC.md` → `docs/reference/NewLang_v0_spec_Draft17_9.md`。
- FormalProof current main/base: `624df3bd4f1f69fc719a1382af44e8170a8ff9a5`。
- F1.3 / F1.4はreview・merge済み/CLOSED。変更前の`lake build`は720 jobsでPASS、`bash scripts/check-proofs.sh`は757 declarationsでPASS。
- branch `f1.5-opaque-root-relocation` はPR #17でreviewされ、mainへmerge済みです。F1.5はCLOSEDです。

正本はcanonical Draftです。local Draft 17.4はhistorical snapshot、bridge/report/Leanはnon-normative encoding/evidenceです。正本、既存F0–F1.4 Lean source/public theorem、pin/manifest/bootstrap/CI workflowを変更しません。

## Modelとscope

`NewLang/F1/Relocation`は既存`Occupancy.SumState`（F1.4 ledger + F1.3 physical placement + F1.2 conditional semantic state）を再利用します。第二のoccupancy/dependency algebraを作りません。

`State.data : PackageId → PackageData`はvalue-owned annotationです。

- `persistentPtrs : List F0.PtrToken`は既存location/incarnation tokenをそのまま保持します。ptr provenanceはblocking dependencyではありません。
- `ownedClaims`は既存ledger上のvalue-owned Storage/slot handleを参照します。surviving packageのhandleが存在しvalue-ownedであること、異なるsurvivor間で重複しないことを`WellFormed`が確認します。
- `opaqueAuthority : Nat`は追加opaque package dataの保存用markerです。Allocation identity、alloc/dealloc authority、新source capabilityを定義するものではありません。一般Allocation ownerの保存・唯一性theoremは今回主張しません。実際のStorage責任とpackage carrier/data保存は証明しています。

対象は既存root-level sum sliceです。F1.1へeraseしたfixed layoutはsingleton root nodeで、そのincarnationはroot incarnationと同じです。任意のaggregate固定descendant tree、nested occurrence、sum lifecycle frontendを追加しません。`erased_fixed_root_is_fresh`は保持した唯一のfixed nodeのfreshnessを証明し、任意subobject treeのfreshnessへ一般化しません。

`Conditions.identified`はcomplete sourceとdestination・size/alignment/layout metadataのcommon identificationを表すcaller premiseです。`aligned`、`prepared`、`canEnd D`はdistinct branchのcaller/platform premiseです。metadata lookup、fallible allocation、callbacksを実装せず、transition前に準備が完了したことをpremiseとします。source/destinationのread/writeは既存Backing access field、raw authorityは実際のStorage claimで検査します。

**Formal representation choices are non-normative.** 有限history/ledger、整数ID、opaque annotation、static `RootSiteLayout`をruntime counter/bitmap/allocator要件にしません。F0.4と同じsite/place対応を使い、placeそのもののglobal historical allocationを新設しません。

## Atomic candidateとidentity

`Action.same`にはfresh allocation parameterがありません。共通identification、live source、same root claimを確認したら`post = pre`、receiptはidentityです。従ってroot/fixed incarnation、current fact、conditional occurrence、placement、governing relation、ptr currentness、carrier、history、accountingのすべてが不変です。ending authority、representation read/write、distinct用dependency guardは要求しません。既存自己occurrence dependencyを持つsourceでも、read/write/ending/preparationがfalseの具体例が合法です。

distinct `Action.move`は`RawMove`による一つのcombined candidateです。

1. source live root / complete typed root claimを消費し、destinationを開始します。sourceとdestinationのnominal region/rangeが異なり、static root locationsも異なるbounded caseです。
2. destination placeはdestination site、root incarnationはhistorically freshです。current/payload factとactive occurrenceには既存`Conditional.FreshAllocation`を使います。historyへ全新IDを記録し、過去IDを一つも落としません。
3. `governingKey = (root incarnation, DomainId)`はderived state relationです。domain identity Dは同じですがfresh incarnationによりkeyはsource relationと異なります。独立のvalue-owned relation IDを追加しません。
4. 同じPackageIdをdestinationへ一度だけinstallします。package table、dependency data、loose carrier、value-owned annotationsは変更しません。source/他survivorのsemantic valueは消えません。
5. source placement relationを終了しdestination extentの新placementを開始します。live backing/domain/type dataは保持します。old ptrはpackage内にそのまま存在しますがstaleです。fresh destination tokenが別に成立し、old tokenをretagしません。

`Receipt.moved`はfresh token/governing keyのproof observationです。最終source syntax/API return designではありません。`CurrentToken`は既存F0 erasure後の`CurrentPtr`と同値です。これはexact incarnationのcurrentnessであり、完全なsafe dereference/access/evidence checkerを実装したという主張ではありません。

`Step = WellFormed pre ∧ RawRelocate ∧ WellFormed post`です。preservationはprojectionですが、RawMoveのfootprint保存・identity非転送・freshness・package frame・stale ptr・old fact終了は別に証明します。公開relationはpre/postのみで、representation copy algorithmもrecoverable中間stateも含みません。concurrency atomicityの主張ではありません。

## Accounting / overlap

F1.4の同じLedger/Accountingを使います。

| 部分 | distinct candidateの責任 |
| --- | --- |
| `D-S` | preのraw Storage claimsをconsumeしfresh destination rootへ |
| `S∩D` | destination rootに含まれ、returned rawと重複しない |
| `S-D` | exactly covering raw Storage claimsとして返す |
| frame | source claim/input raw以外のactive責任を保持 |

`RawMove.occupancy_conserved`は**post WFを前提とせず**raw coverage・fresh claim handle・candidate equationから全ledger footprint等式を証明します。Stepの同じaccounting invariantがcoverageとNoOverlapを確認し、`step_has_unique_byte_responsibility`でscoped各byteの責任がexactly oneと導けます。union保存だけをunique authorityと取り違えません。

具体的partial overlapは同一regionの`S=[0,2)`、`D=[1,3)`です。`S-D={byte0}`、`S∩D={byte1}`、`D-S={byte2}`をkernelで確認します。nested value-owned Storage claimの`[3,4)`はframeとして不変です。その他の合法witnessは同一region disjoint `D=[2,4)`、異なるnominal region `D=region1[0,2)`です。numeric addressはproduction modelにありません。controlだけの同じ数値ラベルからregion identity/authorityを得られないことを確認します。

## Dependency / ptr / address sensitivity

`RawMove.old_occurrence_not_live`と`old_payload_fact_not_live`によりold occurrenceとそのexact payload factはdeadです。package/dependencyがそのままsurviveするため、同じ`Conditional.DependenciesValid post`がsource package・external loose survivorのold-occurrence dependencyをrejectします。relocation専用のad-hoc dependency禁止則、dependency消去、fresh occurrenceへのretargetはありません。独立caseは実際に合法なのでnegative proofはvacuousではありません。

old current-value factもdead、source rootもendedです。old incarnationはhistoryに残り、そのhistoryを保持する後続stateで再allocationできません。既存F0 ptr currentnessとの同値およびfreshnessによりphysical range再利用だけではold incarnationを復活させられません。

embedded self/interior ptr、intrusive link、registry/callback context/escaped copyの自動修復を証明しません。全package dataはunchangedなので、そこに含まれるptrも旧provenanceのままです。explicit fixupはこのtransition外です。Pin/Unpin/Relocatable/Copy/Discardableの新要件を導入しません。

## Erasure

実際のF1.5 `WellFormed`から、次を既存erasure theoremで導きます。erased WFを別premiseとして仮定しません。

```text
F1.5 State.accounted -> F1.4 SumState / SumWellFormed
                    -> F1.3 Backing.SumState / SumWellFormed
                    -> F1.2 Conditional.State / WellFormed
                    -> F1.1 CurrentState / CurrentWellFormed
                    -> F0 State / WellFormed
```

F1.4 projectionはrelocation-specific annotation/persistent ptrの追加precisionを忘れます。下位erasureはledger responsibility/range、placement/access、conditional occurrence精度を順に忘れます。conditional erasureはoccurrence dependencyをprecision-losingに忘れますが、**合法性判定はerase前のexact dependency/accounting state**です。exact Step simulationは主張しません。

## Required negative control inventory

`Counterexample` namespaceだけにbroken endpointsを置きます。下表の名前は`NewLang.F1.Relocation.Counterexample.` prefixです。

| Issue control | declaration | 拒否の理由 / isolation |
| --- | --- | --- |
| 1 reused root incarnation | `reused_root_incarnation_rejected` | historical usedIncarnations membershipがRawMove freshnessと矛盾（任意post/receipt） |
| 2 source placement transfer | `transferred_source_placement_control` | pre/postともWF、targetがsource extentのままなのでexact destination placementに違反。frame ledger等も異なり、唯一の差だとは主張しない |
| 3 copied governing relation | `copied_governing_relation_rejected` | 正常WF endpoint、receiptのrelation keyだけold |
| 4 retarget/revive old ptr | `retargeted_old_ptr_receipt_rejected` | 正常WF endpoint、destinationにold incarnationをretagしたreceiptを拒否 |
| 5 reused current fact | `reused_source_current_fact_rejected` | usedValueFacts freshness違反（任意post/receipt） |
| 6 reused occurrence | `reused_payload_occurrence_rejected`, `retired_occurrence_not_fresh` | currently deadなID9もhistory freshではない |
| 7 duplicated semantic package | `duplicated_package_breaks_only_carrier_rule` | accounting/dependencyは有効、同じinstalled packageをlooseにも置いたcarrier違反 |
| 8 lost semantic package | `lost_semantic_package_rejected` | fully WFなrootless/raw endpointでもold package消失はraw survivor保存と矛盾 |
| 9 raw `S∩D` duplication | `overlap_intersection_raw_duplication_rejected` | shape・exact union coverage有効、byte1のNoOverlapだけ失敗 |
| 10 `S-D` loss | `source_difference_responsibility_lost_rejected` | shape・NoOverlap有効、expected byte0がTotalFootprintにない |
| 11 unconsumed `D-S` raw | `destination_raw_not_consumed_rejected` | shape・exact union coverage有効、byte2をnew rootとrawで二重責任 |
| 12 nominal regions equated | `hypothetical_address_coincidence_does_not_equate_regions` | equal hypothetical labelでもregion/rangeはdistinct、合法moveはdistinct branch |
| 13 same-place end/restart | `same_extent_end_restart_rejected` | fully WF restart endpointでもsame action identityと不一致。equal-range moveもraw differentExtentに違反 |
| 14 public half-state | `public_half_transition_rejected` | old valueはloose、全責任はraw、WFであってもdestination開始がないので公開step不可 |
| 15 implicit address fixup | `implicit_embedded_ptr_fixup_rejected` | owned claims等のWFは有効、ptr dataだけ書き換えるとpackage frameに違反 |

Freshness controls 1/5/6はraw allocation premiseの否定です。malformed freshness candidateが他の全invariantを満たすと主張しません。controls 9–11はledger obstructionを示し、そのledgerのcandidateは既存Accountingを要求するStepにできません。control12は不正region equalityへのminimal contradictionで、numeric-address APIを追加しません。

## FORMAL findings / exclusions

- **FORMAL-ENCODING:** finite ghost history/ledger、exact extent difference、derived `(incarnation,D)` relation key、existing PtrToken/Storage handleのannotations、opaque extra marker、receipt observation。source/compiler/runtime要件ではありません。
- **FORMAL-LEMMA:** raw全footprint保存、live source/destination identity separation、package/data frame、erasure chain、freshness/history、old fact/occurrence dead、same-place legal self-dependent witness、post dependency rejection。
- **FORMAL-SCOPE:** singleton fixed-root + root-level sum、bounded distinct vacant destination sites、Storage claimsによるraw handoff。任意fixed descendant tree/general Allocation owners/dynamic metadata protocol/typed byte validityは省略。保持したfamilyはfreshen/非転送を証明し、このbounded targetをblockしません。
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION:** 検査したDraft 17.9と既存encodingについて新規findingなし。canonicalを補ったり変更したりしていません。

source syntax、production relocation、byte-copy/memmove、numeric machine addresses、overlap-copy implementation、allocator/deallocator、volatile/MMIO operation、concurrency、GC algorithm、Pin system、FFI、LLVM、M9/F2、追加Red Teamを実装しません。

## Build / audit / CI evidence

Lean/Lake **4.34.1**、elan **4.2.4**、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、transitive manifestは不変です。project-only clean（`lake clean newlang-formal`）後の`lake build`は729 jobsでPASSです。`bash scripts/check-proofs.sh`もPASSです。757 baselineを同じ順序で保持し、以下77 public declarationsを追加した**834**をauditしました。project-owned `sorry`/`axiom`/`admit`はなく、許可logic dependencyは従来の`propext`、`Classical.choice`、`Quot.sound`のみです。

**CI結果のevidence pointer:** [Issue #16](https://github.com/wakairo/NewLang_FormalProof/issues/16)のTrack: F review handoffに、open PR URL、current head SHA、`pull_request` eventの`Lean proofs` run/job結果とリンクを記録します。commit自身のSHAを本文に埋めた独立historyは作りません。unchanged workflowはfresh runnerでpinned bootstrap/build/auditを実行します。GitHub APIでexact head/event/completed/successを確認して**F1.5 IMPLEMENTATION COMPLETE / F1.5 READY FOR REVIEW**を記録し、その後PR #17はreview・mergeされました。このclosure自体では後続作業を開始しません。

## 全77 public declaration / canonical clause inventory

以下でprefix `R = NewLang.F1.Relocation`、`X = R.Counterexample`です。列挙した全宣言をproof auditへ追加します。private support lemmaも通常のkernel buildで検証し、呼び出すpublic宣言のauditが推移的logic dependencyを検査します。

### `Model.lean` — 5 declarations

§3/§13.5a/§24.4: explicit conservative erasure of identity, dependency and occupancy obligations

```text
R.wellFormed_erases_to_accounting
R.wellFormed_erases_to_backing
R.wellFormed_erases_to_conditional
R.wellFormed_erases_to_current
R.wellFormed_erases_to_f0
```

### `Proofs.lean` — 31 declarations

§24.4 same/distinct transition, freshness, governing domain, ptr state; §13.5a dependencies; §17.4 unchanged address-sensitive package data

```text
R.same_place_is_exact_identity
R.same_place_is_legal
R.same_place_preserves_token_and_accounting
R.current_token_erases_to_f0
R.RawMove.live_after
R.RawMove.source_ended_destination_started
R.RawMove.destination_root
R.RawMove.other_root
R.RawMove.package_and_authority_data_unchanged
R.RawMove.same_domain_fresh_relation
R.RawMove.destination_does_not_inherit_place
R.RawMove.fresh_incarnation_and_history
R.RawMove.fresh_current_and_occurrence_history
R.RawMove.allocations_recorded
R.RawMove.erased_fixed_root_is_fresh
R.RawMove.old_root_fact_not_live
R.RawMove.old_occurrence_not_live
R.RawMove.old_payload_fact_not_live
R.RawMove.all_survivors_retained
R.RawMove.package_installed_once
R.RawMove.old_token_stale
R.RawMove.old_incarnation_cannot_revive
R.RawMove.fresh_destination_token
R.RawMove.exact_placement_and_backing
R.RawMove.fresh_receipt_not_copied
R.RawMove.embedded_ptrs_and_owned_claims_not_fixed_up
R.RawMove.retired_incarnation_stays_unallocatable
R.step_preserves_wellFormed
R.step_has_unique_byte_responsibility
R.move_rejects_surviving_old_occurrence_dependency
R.no_recoverable_half_state
```

### `Accounting.lean` — 5 declarations

§24.4 occupancy responsibility conservation; supporting §24.3/§24.5 exact responsibility handoff

```text
R.three_way_partition
R.RawMove.source_and_inputs_consumed
R.RawMove.root_and_raw_outputs_produced
R.RawMove.occupancy_conserved
R.RawMove.intersection_never_returned_as_raw
```

### `Counterexample/Model.lean` — 4 declarations

§3/§13.5a/§24.4: direct conditional invariant / dependency support for concrete endpoints

```text
X.singleton_invariant
X.before_invariant
X.after_invariant
X.independent_dependencies
```

### `Counterexample/Accounting.lean` — 3 declarations

§24.4: actual complete F1.4 accounting for disjoint/overlap/distinct-region endpoints

```text
X.stage_accounting
X.independent_before_wellFormed
X.independent_after_wellFormed
```

### `Counterexample/Witness.lean` — 12 declarations

§24.4 legal same/distinct/overlap witnesses, unchanged package transfer; §13.5a old-occurrence survivor rejection; §17.4 embedded ptr boundary

```text
X.raw_move
X.independent_move_is_legal
X.disjoint_relocation_is_legal
X.overlapping_relocation_is_legal
X.different_region_relocation_is_legal
X.partial_overlap_three_responsibilities
X.package_with_embedded_ptr_and_owned_storage_transfers_once
X.before_occurrence_dependencies_valid
X.before_occurrence_wellFormed
X.same_place_requires_no_ending_or_read_write
X.source_occurrence_dependency_rejects_move
X.external_occurrence_dependency_rejects_move
```

### `Counterexample/Controls.lean` — 11 declarations

§24.4 identity/freshness/placement/governing/provenance/package/non-alias controls; §17.4 implicit fixup prohibition

```text
X.reused_root_incarnation_rejected
X.reused_source_current_fact_rejected
X.reused_payload_occurrence_rejected
X.retired_occurrence_not_fresh
X.transferred_source_placement_control
X.copied_governing_relation_rejected
X.retargeted_old_ptr_receipt_rejected
X.duplicated_package_breaks_only_carrier_rule
X.implicit_embedded_ptr_fixup_rejected
X.same_extent_end_restart_rejected
X.hypothetical_address_coincidence_does_not_equate_regions
```

### `Counterexample/Responsibility.lean` — 3 declarations

§24.4 occupancy conservation: isolate S∩D duplication, S-D loss and D-S non-consumption

```text
X.overlap_intersection_raw_duplication_rejected
X.destination_raw_not_consumed_rejected
X.source_difference_responsibility_lost_rejected
```

### `Counterexample/Atomicity.lean` — 3 declarations

§24.4 exactly-once package transfer and unobservable transition: well-formed lost/half endpoints are not legal steps

```text
X.half_endpoints_wellFormed
X.public_half_transition_rejected
X.lost_semantic_package_rejected
```
