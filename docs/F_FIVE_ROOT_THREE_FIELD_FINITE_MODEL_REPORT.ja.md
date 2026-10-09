# Draft 17.30 — five-original-root / three-fixed-field finite conservation model

Track: F

Issue [#41](https://github.com/wakairo/NewLang_FormalProof/issues/41) の有限 Lean adjunct。
停止判定は **F DRAFT17.30 FIVE-ROOT THREE-FIELD FINITE MODEL READY FOR COORDINATION REVIEW**。
候補は OPEN / unmerged PR とし、Coordination review を待つ。
これは production compiler、native heap execution、cJSON North Star の成功証明ではない。

## Authority / historical gate

- FormalProof base main: `c88464d0f0ed36b8e4bcbb7fec63d1e359e5013b`。F #39 / PR #40 が merged、baseline は1399 audited declarations。
- 開始時 Compiler main: `d6f1a7b92c351cd23661ad7714ecb51d29e9468f`。
- 作業中の再確認 Compiler main: `0dcb5c837d70a392503a6163ae0a1f67f515ebc7`。差分は P #237 / PR #240 の source HOLD evidence / fixture / audit。`CURRENT_SPEC`、canonical Draft、Process、Design Procedure、Ledger に差分なし。P の実装・結論を証明の premise にしない。
- `NewLang_Compiler/main/docs/reference/CURRENT_SPEC.md` → **Draft 17.30**。主対象は §3.2b。関連規則は §§3.1–3.4、10–14、16.3、17.1/17.4、26–27。
- 開発運用方針と §4.2、Design Decision Procedure、DI-009/010/013/014 を確認。
- Historical design audit: **N/A — adopted §3.2b の faithful finite proof encoding**。新しい language API / source syntax / normative rule を選択しない。DI-014 の5 original roots / independent fields / six failure worldsを保ち、旧二rootの terminal receiver / durable custody 証明を五root一般証明と読み替えない。

Compiler repository、Draft、Ledger、他 Track の仕様・実装は変更しない。変更履歴は Git を正とし、文書内に独自 Version history を持たない。

## 有限 state と証明境界

`NewLang.Adjunct.FiveRoot` の閉じた `Site = src | a | b | c | dst` と
`Field = next | prev | child` を用いる。general N-root allocator / graph-owner system ではない。

`Origin` は world-qualified な元の root ptr（location / incarnation）、BackingRegion、LifetimeDomain、Allocation binding、Domain binding。
`original world site` はこの有限 proof world の fresh descriptor supply。
その R/O/D/Allocation/location の site injectivity と qualified reconstruction を計算から証明する。
world が違えば branch-local numeric IDs が同じでも証明を流用できない。
値に追加した world tag / identity supply / history は proof encoding であり、runtime representation の要件ではない。

`cell : Site → Option KnownCall.Cell` の None は未allocation。
Some typed / emptySlot / raw / released は、その成功 site の履歴付き stage。
**released は未allocationと異なる**。
`successes` / allocated prefix、owners の List、single optional Claim、release count を別々に持つため、
owner重複・喪失・wrong origin・claim不整合を malformed state として表現できる。
WellFormed は各成功 original の正確な Allocation/Domain carrier と stage/claim/count を要求する。
allocation / field Change / cleanup の候補を実際に計算し、**pre-invariant と operation guard から post-invariant を導出する**。
post WellFormed / post conservation / post release count を operation premise にしない。

### Allocation input の限界

`Allocate` は、固定 source site の `Some(OneBacking)` に続く typed initial snapshot を抽象化する。
next-site、元の qualified descriptor、historically unused initial facts、pre-invariant を確認し、一つの A/D pair と whole typed claim だけを作る。
未成功 site の descriptor metadata が state に存在しても、それ自体は owner、typed root、Storage grant ではない。

これは platform allocator が実際に成功したことや、OneBacking→into_slot→initialize の frontend lowering を証明しない。
その snapshot が source success event に対応することは未証明 adapter / platform boundary。
`reconstruct` の descriptor equality から native allocation success を推論しない。
独立性は arbitrary five-independent-roots premise にせず、この固定 supply と actual sequential success candidates について証明する。

## ONE H と三つの fixed subobjects

全 root claim の type key は同じ opaque completed **H**（0）。
各 root の `layout` は一つの parent place と `next/prev/child` の三つの fixed children。
`structural_fields_form_one_tree` は既存 `F1.TreeWellFormed` を満たすことを示し、
`fields_are_known_disjoint` は既存 structural sibling theorem を利用する。
field ごとに root / Allocation / Domain / whole-region claim を増やさない。
fixed field incarnation / ProjectionId は semantic coordinate であり、field の独立 lifetime-ending authority ではない。
source の `payload:u8` は変更しない opaque Copy scalarとして省略し、数値演算や第四field更新は扱わない。

`selected_H_field_capabilities` は既存 declaration `Derives` の ptr→Option と byte 規則で、
三つの各link fieldとscalarの Copy / Discardable を staticに示す。
**旧 Declaration.Fields は two-field completion に限定される**ので、三link source declaration の completion adapter を証明したとは言わない。
ここでは completed H signature を固定し、whole nominal frontend correctness / incomplete-header transition は対象外。

`FieldRef` は parent RootRef、field selector、nominal ProjectionId の組。
world、元の root ptr、正しい current governing D、typed/live domain、明示した scoped stability loan、AccessLeを要求する。
projection は mode-preserving。read→write に昇格しない。
EndRoot は元の Domain responsibility と、対象 root に active stability loan が無いことを要求する。
loanの開閉はこの finite scoped-block snapshot を表し、scope parser、general lifetime checker、escape analysis を証明しない。

## Change / Reset と uniform dependencies

既存 `F1.Conditional.Fact` をそのまま使い、current parent / selected field value facts、
各fieldの occurrence / payload facts、live Domain facts を `FactLive` に含める。
`dependencies` はこの閉じた profile の **additional surviving semantic observers**。
別の field / sum 専用 dependency vocabulary は作らない。

`changePost` は選択した field と overlapping parent の current fact を freshenする。
Some入力なら selected conditional occurrence / payload fact も fresh。
兄弟field、他root、original R/O/D/A、occupancy claim、permission、loan state は変更しない。
`ChangeGuard` は終了する exact fact に依存する survivor と Unknown alias を拒否する。
`change_preserves_wellFormed` が unchanged survivor を actual post facts に接続する。
`changed_old_occurrence_not_live`、`selected_old_current_fact_not_live`、
`ancestor_old_current_fact_not_live` は old fact の終了を示す。

`usedFacts` / `usedOccurrences` は proof-only ghost history。
Some→Someでptr値が同じでも新しい occurrence は過去未使用であり、old occurrence とは異なる。
未active None入力にも finite plan の unused IDs を予約する保守的 encoding は可能だが、
inactive occurrence は生成・記録しない。本受理証拠の六 source updates / Reset は Some入力に限定する。
これを全ての Option transition の completeness theorem にしない。

Copy locator は original ptr provenance を保つが、blocking dependency / A / D / dereference authority を自動付与しない。
old `Option<ptr<H>>` result は payload value のみで、old occurrence identityを持ち運ばない。
payload-derived refなど、ended occurrenceへのsemantic dependencyは明示的に observer overlayへ入れる。

### Positive と adversarial controls

- independent source writes は legal、各段階で WellFormed。
- 同じアドレスへの A.next Reset は legal、fresh P / field VF / parent VF を持ち、A.prev / A.child は保存。
- old next-Pに依存するlive observerは Reset を拒否。guardを外した candidate も `DependenciesValid` が破れる。
- A.prev-P observerは next Resetを許可。誤った global sibling Reset は old prev-P を失い、同じ dependency invariant に失敗する。
- wrong governing D、read modeでのwrite、swapped ProjectionId、Unknown alias、foreign-world numeric equality はgrantされない。
- issued Copy ptr は失った ownerを修復しない。duplicate Allocation / failure-path lost ownerも invariant を満たさない。

## 六 source updates と pre-detach checkpoint

各 scoped block の loan を閉じながら以下を順に実行する。

| 順序 | 選択field | incoming Copy ptr |
|---|---|---|
| 1 | src.child | A |
| 2 | A.prev | C |
| 3 | A.next | B |
| 4 | B.prev | A |
| 5 | B.next | C |
| 6 | C.prev | B |

`source_update_1..6` は各 actual candidate の ref / history / survivor guard を確認し、
`wired1..6_wellFormed` は generic Change preservation を接続する。
`seven_pre_detach_relations` は六 populated relations と initialized `dst.child=None` を証明。
`five_original_live_roots`、pairwise distinct proofs、`six_updates_preserve_all_originals` を併用する。
A.prev=C は first-child tail shortcut。A.prev=None や head/tailを同一allocationへ置換しない。

これは **source-shaped finite list-policy witness** であり、memory invariant自体が cJSON graph invariantを保証するという主張ではない。
六更新のexplicit historyが指定関係を作れることを示し、production static checkerがその関係を推論できるとは言わない。
B detach/adoptionは行わない。

## Six allocation outcomes / exact cleanup

| First failure / success | 元の成功 prefix | 明示 cleanup order | frees |
|---|---|---|---|
| #1 src failure | ∅ | ∅ | 0 |
| #2 A failure | src | src | 1 |
| #3 B failure | src,A | A,src | 2 |
| #4 C failure | src,A,B | B,A,src | 3 |
| #5 dst failure | src,A,B,C | C,B,A,src | 4 |
| all success | src,A,B,C,dst、六更新後 | dst,C,B,A,src | 5 |

各cleanupは **EndRoot→empty slot→full Storage→finalize original D→deallocate original A**。
`Cleanup` は各primitiveの guard を別々に要求する。
`ActualCleanup` は fixed five-site source listの各 transitionを記録する。
`outcome0..5_actual_cleanup` は各入力 stateで元の A/D を実際に用意し、前段 post-WFから次段 applicability を証明する。
単に complete post tableを仮定したり、implicit destructor / Dropを置いたりしない。

`root_slot_raw_conservation` は同じ full extent の責任が一つの claimで移り、
A は最後の releaseまで、D は finalizeまで保持されることを示す。
`cleanup_frames_other_root` は対象外の元の root / authority / claimを維持する。
`each_success_freed_once_absent_never_granted` は成功 original は released/count=1、
未成功 original は cell=Noneでgrantなし、全ての最終 owners/claimsが空であることを示す。
`exact_zero_to_five_frees` は各pathの総countを0,1,2,3,4,5に確定する。

元の backing の disjoint abstract bytes と full Extent footprint は既存 Backing.World / Geometry / Extent で証明する。
容量1は一つのwhole-H abstract extentのproof coordinateで、sizeof(H)、field offset、C ABI、native address ではない。
この有限 claim accountingを arbitrary `F1.Occupancy.Accounting` / live physical-world evolutionへ接続する operational adapterは未証明。

ended field link / occurrence data は ghost archiveとして残るが、Typedでないrootのfactsは`FactLive`から除く。archiveへの数学的projectionはsourceのdereference permissionではない。

stored Copy ptr linksはcleanup中にdanglingになり得るが、blocking observerを自動生成しない。
`copied_links_do_not_block_explicit_cleanup` は linksを変更せず全五rootを明示的に解放できることを示す。
ended rootの reloan、wrong Domain、mismatched Allocation / full extent、二重release は拒否する。
active scoped ref / semantic observerを持つrootの終了は EndGuardが拒否する。

## FORMAL findings と unproved boundaries

| 分類 | 判定 / 範囲 |
|---|---|
| FORMAL-ENCODING | five closed sites、three fixed sibling selectors、world-qualified original descriptors、one A/D ledgerとone full claim/site、proof-only historiesで符号化。arbitrary malformed statesも表現可能。 |
| FORMAL-LEMMA | computed injectivity / reconstruction、known sibling disjointness、Changed ended-fact lemmas、pre→post invariant preservation、exact original primitive guards、all six concrete tracesを追加。 |
| FORMAL-SCOPE | actual allocator/OneBacking success、three-link nominal frontend completion、source checker/alias analysis、exact H ABI/size、physical heap executionへのrefinementは未証明。既存Declaration two-field proofの一般化を宣言しない。 |
| FORMAL-SCOPE | B detach/adoption/custody、general N-root allocator/Owner graph、F3.1全体、concurrency、LLVM、FFI、native/cJSON North Star成功は対象外。 |
| FORMAL-HOLE / FORMAL-AMBIGUITY | 本bounded subsetでは検出なし。canonicalを補強・変更しない。 |

忠実な finite witnesses / rejection controls の結果を Coordination に渡す。
production P #237のsource HOLDをこのLean結果で覆さない。P / Rの判断や作業を代行しない。

## Verification / CI handoff

- baseline main: `lake build` PASS、proof audit **1399** PASS。
- candidate: `lake build` PASS、全existing public statements / model filesを保持。
- `bash scripts/check-proofs.sh` PASS: **1512 declarations = 1399 retained + 113 new**。
- project-owned Lean sourceに `sorry` / `axiom` / `admit` なし。
- 許可依存は従来どおり `propext` / `Classical.choice` / `Quot.sound` のみ。audit whitelistを拡張しない。
- Lean / Lake **4.34.1**、elan **4.2.4**、mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612**。toolchain / manifest / bootstrap / CI pinは変更なし。
- 既存 `Lean proofs` の push と pull_request workflow を使用。candidate exact head、双方のrun/job結果、PR OPEN / unmerged状態は [Issue #41 handoff](https://github.com/wakairo/NewLang_FormalProof/issues/41) に記録する。pushはsource headをcheckoutし、pull_requestはGitHubのtest merge commitをcheckoutするため、両者を区別して確認する。

以下が追加auditの全inventory。private helperはこれらのkernel-checked proofとaxiom reportsを通じて検査する。

### Model/proof — 42 declarations

Namespace: `NewLang.Adjunct.FiveRoot`.

```text
site_code_injective
field_code_injective
projection_injective
field_place_injective
parent_place_injective
parent_ne_field
original_region_injective
original_incarnation_injective
original_domain_injective
original_allocation_injective
qualified_origin_reconstruction
fields_are_known_disjoint
allocation_preserves_wellFormed
allocation_has_one_original_pair
allocation_preserves_previous_origin
mode_preserving_projection
readonly_projection_cannot_write
change_preserves_original_memory
change_frames_sibling
change_frames_other_root
change_preserves_wellFormed
some_to_some_starts_fresh_occurrence
occurrence_dependency_rejects_reset
unknown_alias_never_grants_replace
wrong_projection_never_grants_replace
withLoans_wellFormed
cleanup_available
endRoot_requires_original_domain
release_requires_original_allocation
cleanup_target
cleanup_frames_other_root
cleanup_preserves_wellFormed
root_slot_raw_conservation
double_release_rejected
changed_old_occurrence_not_live
selected_old_current_fact_not_live
ancestor_old_current_fact_not_live
field_ref_has_parent_identity
copied_option_has_no_occurrence_envelope
original_location_injective
structural_fields_form_one_tree
selected_H_field_capabilities
```

### Finite fixtures / negative controls — 71 declarations

Namespace: `NewLang.Adjunct.FiveRoot.Counterexample`.

```text
empty_wellFormed
allocate_src
prefix1_wellFormed
allocate_a
prefix2_wellFormed
allocate_b
prefix3_wellFormed
allocate_c
prefix4_wellFormed
allocate_dst
prefix5_wellFormed
five_original_live_roots
five_originals_pairwise_distinct
original_backings_disjoint
source_update_1
wired1_wellFormed
source_update_2
wired2_wellFormed
source_update_3
wired3_wellFormed
source_update_4
wired4_wellFormed
source_update_5
wired5_wellFormed
source_update_6
wired6_wellFormed
seven_pre_detach_relations
six_updates_preserve_all_originals
same_address_reset_legal
reset_wellFormed
reset_freshens_only_next_occurrence
observedNext_wellFormed
stale_payload_ref_rejected
global_reset_erases_sibling
broken_global_reset_rejected
read_mode_write_rejected
swapped_field_id_rejected
wrong_governing_domain_rejected
unknown_alias_rejected
equal_numbers_foreign_world_rejected
issued_ptr_does_not_repair_missing_owner
duplicate_allocation_rejected
actualCleanup_preserves_wellFormed
outcome0_actual_cleanup
outcome1_actual_cleanup
outcome2_actual_cleanup
outcome3_actual_cleanup
outcome4_actual_cleanup
outcome5_actual_cleanup
all_six_outcomes_are_actual
all_six_outcomes_wellFormed
all_six_clean_exits_wellFormed
each_success_freed_once_absent_never_granted
exact_zero_to_five_frees
lost_owner_on_failure_rejected
wrong_domain_cannot_end
mismatched_allocation_cannot_free
full_extent_mismatch_cannot_free
deallocate_twice_rejected
no_reloan_after_end
copied_links_do_not_block_explicit_cleanup
observedPrev_wellFormed
disjoint_sibling_observer_allows_reset
unguarded_reset_invalidates_survivor
scoped_ref_blocks_end
abstract_full_extent_footprint
abstract_geometry_compatible
original_full_extents_disjoint
live_root_and_empty_slot_never_coexist_at_a
duplicate_domain_rejected
mismatched_domain_cannot_finalize
```
