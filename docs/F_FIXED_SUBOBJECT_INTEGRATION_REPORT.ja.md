# Fixed-subobject Change / parent-sibling preservation integration

Track: F

## Authority / bounded task

[FormalProof Issue #29](https://github.com/wakairo/NewLang_FormalProof/issues/29) の F-A〜F-E を対象とする adjunct evidence。
`NewLang_Compiler/main` の [開発運用方針](https://github.com/wakairo/NewLang_Compiler/blob/355f1d2d1621cb5760b9dae7e9931753eedcc9f6/docs/NewLang_Project_Development_Process.md) を確認した。

| Authority | 検証した main / source |
| --- | --- |
| Compiler | `355f1d2d1621cb5760b9dae7e9931753eedcc9f6` |
| CURRENT_SPEC | [Draft 17.19](https://github.com/wakairo/NewLang_Compiler/blob/355f1d2d1621cb5760b9dae7e9931753eedcc9f6/docs/reference/NewLang_v0_spec_Draft17_19.md) |
| FormalProof base | `b3df0fc3f9a44f7afd41f835dc007dc1cada29ba` |
| Branch | `f-fixed-subobject-integration` |

両 main は作業開始時の公開 HTTPS Git 読み取りで上記 SHA と一致した。Draft §3.8、§13.5a/§13.5b、§14.4、§17.4 と既存 F1.1 を照合する。Draft 17.4 は historical snapshot のまま変更しない。未merge の stable-root PR #28 は parent branch / proof input / normative evidence に使用しない。

本 task は source field syntax の裁定を待たず、既存 semantic definitions 上の bounded integration を調べる。F3.1 や新しい broad milestone は開始しない。

### Merge-order synchronization note

Coordination review後、先行するstable-root PR #28がmainへmergeされたため、このbranchはそのreview済みmainへ追随した。fixed-subobject theorem/control本体は変更せず、import / README / proof-audit listを合成した。FormalProof baselineは992 audited declarationsとなり、本adjunctの15件を加えたexact branch auditは1007件である。

## F-A — representability inventory

| 問い | 分類 | 既存 interface と今回の evidence |
| --- | --- | --- |
| aggregate/fixed parent-child identity | already modeled | `StructuralLayout.path`、`Parent`、`Ancestor`、`TreeWellFormed`。root metadata は一つで child に occupancy/domain copy を置かない |
| field Change と root/field incarnation 保存 | already modeled | `RawStructuralReplace` / `RawStructuralStore` と all-incarnation frame。今回 identity+liveness をまとめた integration theorem を追加 |
| ancestor current-value change | already modeled | `affectedBy` は semantic overlap を使い、target/ancestor/descendant を refresh。今回 old ancestor fact の死亡と history 保存を同時に導出 |
| known-disjoint sibling current fact/value | composable from existing definitions | disjoint current-fact frame + target subtree 外 local fragment frame。今回一つの theorem と legal witness に統合 |
| dependency overlap/disjointness | already modeled | exact `Fact.valueFact PlaceId ValueFactId`、`LocalDeps`、derived `SubtreeDeps`、candidate-post `CurrentWellFormed` |
| coarse finite dependency set | composable from existing definitions | exact blockers を含む larger Finset の subset reasoning。追加した superset theorem と二atom control |
| F1 structural Unknown effect adapter | missing modeling hook | F1.1 には abstract `Unknown` effect/summary、concretization、effect-to-transition adapter がない。F2 の generic `May.unknown` と safety evidence は存在するが F1 field effect adapter を証明していない |
| field ptr point acquisition | missing modeling hook | F0 `PtrToken` は root location+incarnation。F1 `StructuralTarget` の place と child incarnation を結ぶ ptr issuance/acquisition relation がない。Backing `AccessPtr` も root-only token を包む |
| structural EndRoot → descendant ptr rejection | missing modeling hook | F1.1 `CurrentState` の rich fixed-tree take/destroy と descendant-token acquisition がない。flat F0、flat Backing、rich conditional sum の lifetime slices から逆向きに推論しない |

canonical contradiction / genuine formal ambiguity は見つからなかった。missing hook は current proof coverage の境界であり、canonical が field ptr を禁止するという意味ではない。

## F-B — integration theorem inventory

`NewLang/F1/FixedChange.lean` の namespace は `NewLang.F1.FixedChange`。新しい operation / generic effect framework / pointer datatype を定義しない。

| 新しい audited theorem | 成果 |
| --- | --- |
| `field_replace_preserves_target_and_root_identity` | proper field target の layout、target/root incarnation、governing domain、enclosing carrier を保存 |
| `field_replace_preserves_target_incarnation_liveness` | target は live node のまま、同じ exact incarnation が live |
| `field_replace_frames_known_disjoint_value` | sibling current fact、local content/dependencies と exact fact liveness を保存 |
| `field_replace_refreshes_ancestor_and_ends_old_fact` | ancestor の historically fresh fact、old fact の非live、old/new history recording |
| `field_replace_rejects_returned_target_dependency` | returned old field value に残る own-current dependency は reject |
| `field_replace_rejects_surviving_overlapping_dependency` | target/ancestor/descendant の old fact に依存する unchanged survivor は reject |
| `field_replace_dependency_superset_keeps_blocker` | larger finite dependency set に retained された blocker は消えない |
| `field_replace_allows_enclosing_root_ptr_acquisition` | rich checked field replace の post から sound state erasure で enclosing root-only ptr の point acquisition を導出 |
| `erased_field_incarnation_cannot_acquire_as_root` | live exact field incarnation を erased root-only ptr interface に渡しても acquire できない。missing hook の局所化 |

incarnation / sibling / ancestor の operation equations は **Raw** relation から導き、post-WellFormed oracle に隠していない。surviving dependency rejection は old fact death と candidate-post dependency invariant から導く。legal positive controls は concrete post の各 invariant を既存 fixture checker で証明する。

root ptr theorem は既存 `AcquireRef` を使う **point-of-acquisition** evidence。new state での stability/access premises を caller に要求し、persistent ref の将来使用まで保証しない。field ptr theorem の代用ではない。

EndRoot contrast は既存 main の `F0.stale_ptr_after_take_cannot_acquire_ref` / `stale_ptr_after_destroy_cannot_acquire_ref` と同一配置での reinitialize rejection が引き続き audited。これらは flat root の contrast として使用できるが、F1 fixed descendant の EndRoot/acquisition simulation は未証明。

## F-C — concrete controls / dependency results

既存 finite tree fixture をそのまま再利用する。

```text
root p0
├── a
│   ├── x   ← leaf Change target
│   └── y
├── b
│   ├── bx
│   └── by
└── c       ← external survivor owner
```

`content` は各 node の local fragment token。ancestor の local token が不変でも、subtree から組み立てる semantic value と current fact は変わる。この区別を cached aggregate value の不変と読まない。

追加した六つの controls は `NewLang.F1.Counterexample.Transition` 内に置き、既存 private fixture を重複作成しない。

| 新しい audited control | 結果 |
| --- | --- |
| `field_change_preserves_parent_identity_and_refreshes_ancestor` | legal leaf replace、root/field incarnation 保存、old root/field fact 死亡、ancestor local content frame を同時に証明 |
| `sibling_value_and_dependency_survive_field_change` | legal disjoint-dependent replace、sibling content 不変、依存する sibling fact は live |
| `surviving_parent_value_dependency_blocks_field_change` | well-formed pre で `c` が `Value(p0)` をcarryすると `Change(x)` は全 candidate に対して reject |
| `larger_finite_dependency_set_keeps_parent_blocker` | `c` の dependency が `{Value(b), Value(p0)}` でも parent blocker を保持して reject |
| `field_change_keeps_enclosing_root_ptr_acquirable` | fresh ancestor fact と同じ root incarnation を持つ post で root ptr acquisition が legal |
| `live_field_identity_cannot_be_acquired_through_root_only_erasure` | field incarnation は rich state で live だが erased root token では取得不能という concrete witness |

既存の以下も維持する。

- `replace_rejects_old_self_structural_dependency` / `ancestor_local_dependency_is_preserved_and_rejects_replace`: surviving `Value(field)` は Change(field) を block。
- `disjoint_dependency_replace_is_legal`: known-disjoint **dependency source** は block しない。dependency の owner が disjoint なだけでは source overlap を否定できない。
- `old_self_dependency_rejects_structural_replace_but_allows_store`: old-only dependent value を atomic store が消費する場合は legal。従って「Value(field) が常にあらゆる Change を block」とは主張しない。
- `overinvalidating_sibling_rejects_an_otherwise_legal_replace`: sibling を誤って invalidate すると依存する otherwise-legal survivor が reject される negative control。
- F2 `unknown_is_not_dependency_free` / `Counterexample.unknown_retains_concrete_blocker`: 既存 Unknown は possible dependency を empty としない。

最後の F2 evidence は **F1 の Unknown effect adapter の証明ではない**。今回 structural 側で machine-check した coarse result は finite superset / overlapping-parent blocker まで。F1 effect-summary Unknown を state operation に結ぶには concretization + preservation/disjointness certificate + sound legality adapter が必要で、未実装として明記する。state-dependent erasure が sibling fact を root fact にまとめることを、逆方向の operational legality permission にしない。

## F-D — aliasing write capability

`RawStructuralReplace` / `RawStructuralStore` / `RawStructuralSwapDistinct` を確認した。write/type obligations は abstract `Prop` で、`exclusive ref`、alias-count、unique writer、lifetime-ending authority を要求する field はない。same-place swap の ordinary write premise も同じである。

swap の `StructuralTargetsDisjoint` は simultaneous **mutation target** 間の applicability 条件であり、他の全 live write ref を排除する exclusivity 条件ではない。existing `CarrierUnique` 等は semantic package carrier の一意性であり、write authority の排他性ではない。

abstract `canWrite` に caller が何を入れるかは未形式化であるため、source ref derivation / production checker が ordinary write を exclusive に誤変換しないことまで証明したわけではない。current model 内にその mismatch は見つからず、semantics patch は行わない。

## F-E — no-foreclosure / addability

- **nested fixed aggregate**: finite path layout は depth 1 に制限されず、今回 depth 2 の `x` fixture と既存 nested replacement / aggregate sibling swap の witnesses を再利用する。arbitrary finite layout の general frame theorem は対象の exact relation に依存する。recursive Node / unbounded dynamic allocation の proof は含まない。
- **ptr-valued field**: `ValueFragment` は opaque local content+dependency。現在 `Nat` token は payload semantics/ABI を固定せず、field の kind を non-pointer に制限する premise もない。将来 typed/opaque ptr payload と target/place/incarnation relation を加えることを妨げない。現時点では content を decode して ptr provenance、safe issuance、field acquisition、recursive Node を保証する theorem はない。

## FORMAL findings

- **FORMAL-LEMMA**: 既存 F1.1 の equations/guards を組み合わせると parent identity / ancestor fact death / sibling value frame / finite-superset blocker を同時に証明できる。今回 15 declarations を追加した。
- **FORMAL-ENCODING — missing modeling hook**: exact field ptr acquisition と fixed-tree EndRoot adapter が欠ける。最小 witness は one root+one live child、異なる incarnations。erasure は root incarnation のみ残し、child incarnation を root token に渡すと acquire が拒否される。canonical field ptr prohibition ではない。候補は field-aware token/target relation と separately reviewed root-ending adapter を追加する bounded task。
- **FORMAL-ENCODING — missing modeling hook**: F1 Unknown effect adapter / concretization がない。finite may-set blocker と F2 Unknown safety を別々に証明できても、それだけで production summary correctness を主張しない。
- **FORMAL-SCOPE**: ordinary ref aliasing derivation、ptr-valued payload decoding、rich fixed-tree lifetime integration は addable な別 task。今回 policy を発明して埋めない。
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION**: 今回の bounded comparison では発見なし。canonical 変更なし。

## Verification / review handoff

- main baseline: `lake build` **PASS**、proof audit **992 PASS**。
- branch: `lake build` **PASS**（774 jobs）、`bash scripts/check-proofs.sh` **1007 PASS**（992 existing + 15 new）。
- project-owned `sorry` / `axiom` / `admit` はなし。許可依存は従来どおり `propext`、`Classical.choice`、`Quot.sound` のみ。
- Lean `v4.34.1` / mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` / bootstrap / manifest / workflow は不変。
- unchanged workflow `Lean proofs` が branch push / pull_request を検証する。exact final head の GitHub CI と PR status は Issue #29 handback に記録する。local PASS だけを remote CI PASS としない。
- Issue は Coordination review 用に open のまま、作成した PR は unmerged のままとする。review-readiness marker は実際の publication/CI evidence と scope limitations を伴って handback する。

No F3.1/global theorem、source syntax、compiler code、field implementation、recursive Node、raw storage/allocator、cJSON、canonical Draft edit。本 adjunct の後続実装には進まない。
