# F62 — 二つの元root・名前付き呼出し・二正常分岐joinの有限adjunct

Track: F。NewLangの言語意味論・所有値管理の品質検証。

**CONDITIONAL FINITE LEAN ADJUNCT PROVED — UNSELECTED SOURCE/COMPILER BRIDGE**。
これはIssue [#62](https://github.com/wakairo/NewLang_FormalProof/issues/62)の単一proof-only adapterである。Leanの入力条件を満たすモデル状態についての証明であり、NewLang source acceptance、Productionの証明発行、C17/native、製品PASSの証明ではない。

## Authority・事前予測・実測

- FormalProof/main `a8de4ebb4099f4742fc161d26867740dcac48414`、base tree `8927eb08eda0e00390e1758660ea0a47f8f8f7a1`。branch `f62-named-call-match-join`。
- Compiler/main `d6e603e12591c2ff39e3e1b77c784681fec66033`。CURRENT_SPEC blob `50c96b8c2891aa0f2b53571d8734c5cf796d0d6a` → Draft17.30、spec blob `db8fe08f811acc8286f2d37e9d3229b5d7a67067`。固定treeで照合し、既存ローカルspecと同じblobであることも確認。
- Issueが指定するP478 / DRAFT PR479 head `03b1751b513e7aef2d7ba193eda671a556f54b47`は、call-in-match source CHECK・source-issued call effect certificate・C17/nativeの成功証拠ではない。Pの実装をLean premiseにしていない。
- Process §§4.1.1/4.2/4.3.1/6、Compass、Design Procedure Gates A–C、既存F1 fixed-field/conditional occurrence、F3.0契約とone-root SumLifetime、F59報告、FiveRoot有限fieldモデルを確認。F3.0契約はglobal soundness theoremの実装ではなく、SumLifetime pilotもtwo-root fixed-field call adapterではない。
- **予測**：既存Change/Reset保存lemmaは再利用できるが、actual/formal substitution・branch join・source発行済み権限の接続は既存coreだけから出ない。代替はvisible bodyの有限再解釈、明示的effect certificate、最初の不足でHOLD。
- **選択と実測**：visible bodyを一つに固定して再解釈し、source入力義務を明示した1 moduleで前二者を構成できた。新しい一般kernelやcompiler certificateは作らず、source bridge不足は残す。事前のmodel/expected setは変更せず、ローカルの型注釈・proof elaborationを修正した。初回失敗ログは作業領域に保持。

## 一つの有限モデル

実装は[NamedCallJoin.lean](../NewLang/Adjunct/NamedCallJoin.lean)。既存`FiveRoot.Replace/changePost`だけをmemory updateとして使い、accepted F0/F1/F2や既存adjunctは変更しない。

具体例は既存`prefix2`の**二つだけのtyped original**、site `src`をH、`a`をTとして使う。追加の三siteは未allocationのまま。元のworld-qualified O/R/D/Allocation/domain-bindingとwhole-root claimは既存MemoryInvariantで検査する。これは既存typed-success snapshotの有限解釈であり、実allocator/initializeのsource生成証明ではない。

`Entry`は次を明示的に要求する：

- PRE WellFormed、H≠T、typed supportはちょうど{H,T}、正しいcurrent H.next read refとT.next nonexclusive write ref。
- 既にopenなcaller blockのloan snapshotは{H,T}。このloanをF59から生成したとは主張しない。
- saved Copyの値は実際のPRE `H.next`。Some(q)なら元のissued locatorであることを検査。Copyからroot/Allocation/Domain権限を得ない。
- saved Copyとcalleeが返す旧T.next Copyの全memory dependencyが既存surviving observer overlayに含まれること。さらに全生存値・記憶のscope dependenciesを供給すること。

`entry_checks_distinct_original_identities`はPREの実際のtyped cellsとMemoryInvariantからoriginal descriptor対応、DとAllocationの別identityを導く。元rootのidentityを都合のよいPOSTへ新設しない。

### 名前付きcallと実仮対応

唯一のbodyはconceptual `set_next(dst,q) = replace(dst@next,Some(q))`で、旧T.next Copyを返す。`FunctionName.setNext`の解釈を`Call`の定義で固定する。一般ASTのDefinitionCheckedやsymbol resolverではない。

`Mapped`はformal target、FieldRef全体（world/ptr/current incarnation/Domain/mode/field/ProjectionId）、locator値、memory dependencies、scope dependenciesをactualと同一にする。型signature一致だけで権限を付与しない。callee bodyには同じPREの既存`Replace`、fresh plan、`ChangeGuard`が必要で、POST WFを入力に置かない。

`checked_call_constructed`はEntry・実際のSome(q)・freshness・survivor guardからこのcallを構成する。変更はformal側のtarget/ref/valueを使うため、対応検査が無ければcallerの別rootを更新し得る。frameと旧戻り値の証明に対応等式を使用する。

### 二正常分岐と合流

`Run.none`はsaved H.next=Noneのno-write。`Run.some`はsaved=Some(q)の名前付きcall。一回の正常call/bodyに限定し、例外・Unknown・recursionや一般function semanticsは扱わない。

`before_call_after_call_join`は両constructorを検査し、computed candidateからWF、元の全cells/origins/owners/claims/world/permission/loans/dependency overlayの同一性、H.next、Tの無関係なsiblings、二つのCopyとscope metadataの保存を導く。

T.nextのcurrent factとoccurrenceは**旧候補と新候補の有限集合**に保持する。Some枝のnew occurrenceとNone枝のold occurrenceを等しいと仮定しない。`call_resets_old_occurrence`はSome→Someでも旧Pがliveでなく、新P≠旧Pであることを既存theoremから導く。root ptr / fixed field identityを取り替える操作ではない。

`joined_keeps_original_write_ref`は同じactive scope中の元のwrite refのpoint validityを保存する。これは新Domain grantでも、scope終了後のref再利用でもない。`joined_saved_copy_remains_exact`と`joined_preserves_two_originals_and_copy_dependencies`はH.nextの旧Copyと全memory dependencyの保存・実際のPOST livenessを示す。

### scope終了

`Finish`はactive phase、saved/returned Copyと全surviving-memory scope dependencyのnonescapeを検査し、computed close後もCopy/dependency dataをそのままforwardする。loan snapshotだけを空にしてphaseをclosedへ進める。

`finish_preserves_and_ends_refs`はWF・元owners/root claims・Copy/overlayの保存と、終了後にそのsnapshot上でRootRefValidを得られないことを導く。二重終了も拒否する。既にopenな**一つのblockに属する二ref**の有限終了であり、global scope freshness、nested scopes、一般borrow checker、実source評価/escape解析の証明ではない。

## 三つの主要positive evidence

| Lean evidence | 実際の構成 |
|---|---|
| `Witness.some_call/some_normal_path` | H.next=Some(ptr_T)、T.next=Some(ptr_H)。calleeがT.nextをSome(ptr_T)へ変更。旧Some(ptr_H) Copyを返し、Hの旧Some(ptr_T) Copyは不変 |
| `Witness.none_normal_path` | H.next=None、同じ元T.next=Some(ptr_H)。call/writeなしで正常終了 |
| `Witness.two_normal_paths_join/finite_normal_join` | 二つの正常outcomeに共通の元owners・旧戻りCopy・非空DomainLive依存を保持。T.next payload/fact/occurrenceの旧/新候補を両方保持 |

`Witness.both_normal_paths_close_preserving_originals`は両block終了後も元のownersとCopyを保存し、終了refを再使用できないことを確認する。具体例のdependency overlayは**空ではなく{DomainLive(D_H)}**。各pathでlive factのまま残る。

## 独立negative controls

| control | 拒否される理由 |
|---|---|
| `Witness.swapped_original_actual_rejected` | actualはT、formalをHへ差替えた対応が不成立 |
| `Witness.wrong_field_actual_rejected` | actual/formal双方を同じprev refにしてもnext bodyに使えない |
| `Witness.stale_actual_rejected` | actual/formalを同じstale incarnation99にしてもcurrent T refにならない |
| `Witness.dropped_hidden_dependency_rejected` | 値とrootが一致してもformal側で非空memory dependenciesを空へ落とせない |
| `Witness.surviving_old_occurrence_rejected` | actual旧T.next occurrence100へのsurviving observerがResetを拒否。`conflict_entry_memory_wellFormed`はそのPREがWFであることも証明 |
| `Witness.invented_third_root_rejected` | 出力へ未allocation dstのtyped cellを追加してもRunにならない |
| `Witness.overwritten_old_some_copy_rejected` | 返すべき旧Some(ptr_H)をNoneへ上書きしたoutcomeを拒否 |
| `Witness.old_some_occurrence_cannot_return_as_current` | Some call後に旧P100をcurrentとして復活できない |
| `Witness.double_scope_end_rejected` / `surviving_ref_escape_rejected` | 二重終了・生存memoryへのref escapeを拒否 |

generic controlsはread→write昇格、返却Copyのscope escape、誤ったref対応も拒否する。ordinary非排他writeの重複自体を禁止する新規規則は加えない。実際の変更とsurviving dependencyの衝突を検査する。

## 証明済み・仮定・未証明adapter

**証明済み**：このclosed bodyと有限entry/event規則に対する実仮対応、Change/Reset、元owner/root保存、二正常分岐join、Copy/依存の非消去、checked lexical finish、上記負例。

**明示したsource-interface仮定**：typed-success snapshotのsource対応、現在の元root/Domain/ref/accessの発行、H.nextのlocator provenance、全memory hidden depsとscope depsの正しい供給・coverage、実calleeがこのvisible bodyと同じであること。これらはLeanのEntry/Call interpretationとして検査する条件であり、実sourceが自動的に供給できることは証明しない。unchecked/unsafe issuerを暗黙のpremiseにしない。

**残る公開compiler certificate / refinement**：callee symbol/body identity（hash等）、formal parameter roleとactual original O/R/D/Allocation/current binding対応、nominal field/projectionとmode、current incarnation/provenance/write evidence、返却される旧Copyの値とhidden deps、Change/Reset invalidation/fresh historyと全survivor deps、二正常edgeのconservative may/must join、scope exit/current carrierとnonescapeを実際のsource/checkerデータから発行・検査する接続。本moduleがそのProduction certificateを実装・検証したとは言わない。

FiveRootのclaims/frameはその既存有限モデル内の責任であり、今回新たに一般F0/F1 occupancy Accounting refinementや実native heapまで接続したものではない。F59 typed-root/Domain-value registry seam、任意AST/hidden heap/effects、global F3.1も未証明のまま。

## 検証・停止

新規module **84 explicit declarations / 46 theorems**を全て既存proof auditへ一度ずつ追記。baseline2194を維持して計**2278 reports**。audit enforcement/allowlist、Lean `v4.34.1`、mathlib/manifest、workflowは無変更。project-owned placeholder/custom logical assumptionsは追加しない。

単体`lake env lean`成功。全`lake build`と`scripts/check-proofs.sh`、一回の通常push/PR CI cycleの実測、candidate head/treeはDRAFT PRとIssue #62最終報告へ記録する。CIがgreenになるまでのretryやcandidate変更は行わない。

Historical audit: **N/A — Draft17.30 §§13.5a/13.5c/17.4/18/26のfaithful finite proof representation; no language rule changed**。DI009/010/014の独立original authorityとmode-preserving fixed projection、DI011のbody-sensitive actual call義務はKEEP。general source/effect/registryはDEFER。Ledger変更不要。旧M9全文は網羅調査していない。

Compass / Process §4.3.1上も限定探索の証拠であり、監査局所性の製品効果・通常caller負担の削減は未実測。機構成功をProduct GOへ昇格しない。H1 #268、STB F45/M374 HOLDは維持。目標逸脱として別の大型mechanism投資を提案せず、Coordinationに未証明adapterの判断を残す。

2026-10-15 22:02 JST開始、Issueの約60–120min予算上限内で構成・監査・一回の公開/CI・一度のIssue報告に限定。報告後直ちに停止。自己merge/close、compiler/canonical変更、他Track起動は行わない。
