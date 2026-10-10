# F #55 — Some OneBacking から exact empty slot への限定 refinement

結論：F #53 の trusted source-builtin Some POST から、Some 消費、OneBacking 全体の destructure、full raw の into_slot 消費を別々の source step として構成した。対応する accepted `RawIntoSlot` / `consumeOne` と post `Accounting` / `WellFormed` を導出した。original A は同じ source value と rich R interpretation のまま AVAILABLE、current slot は一個、old raw-only C frame は保持される。これは **source specification→accepted rich custody の条件付き証明**であり、production Compiler の検証ではない。

## 固定 authority・限定範囲

- FormalProof base/main `1c8e02b3e85fd74fe4055114fb343f2522640352`。F #53 PR #54 の guarded merge と [Coordination review](https://github.com/wakairo/NewLang_FormalProof/pull/54#issuecomment-6097480180) を起点とする。
- Compiler main `b75baea96a644e68634baee383299b66981b3c62`、canonical Draft 17.30 §§3.1–3.4、§4、§13–14。§3.2 の実際の heading は `Draft 17.24 bounded allocated recursive root source profile`。§3.4 は exact length / alignment / backing liveness / raw occupancy を要求する。
- 一個の closed completed Node、PRE grant 最大一個、一回の Some/None issuer とその直後の slot conversion のみ。old C は raw-only、typed lifetime root は存在しない。
- Draft17.31 / DI-015 / Compiler PR #273 は proposed / MERGE HOLD。P #289 の結果には依存せず、他Trackを起動していない。
- 新しい canonical rule / source grammar / accepted F0/F1 の変更はゼロ。Historical Process §4.2 の no-foreclosure を維持する additive proof adjunct。法的source effect/call ruleの採用には独立 M Gate A–E が必要。

## PRE 仮定と POST 導出の分離

| 境界 | 仮定・信頼入力 | 導出した結果 |
|---|---|---|
| 発行 | accepted F53 の `SourceWF`, rich WF, `Refines`, PRE grant ≤ 1、aligned `Success`、fresh/history-disjoint `Supply`、`Supply.n = sizeofH` | `issuer_to_slot` は F53 Some event と issuer POST を構成してから successor を証明。新しい A/full raw/slot/carrier の POST は PRE 仮定にない |
| nominal / layout | `Typing.node` は選択済み Node の静的 rich TypeId 対応。`Typing.size` は authorized layout と sizeofH の対応 | full Has の長さは issuer 由来。alignment は issuer Success 由来。与えられた Node TypeId の exact-size conversion を構成 |
| source移転 | `Context` は read-only issuer provenance。`Custody.current` が sole current graph。新しい abstract `Step` / `SourceWF` は source-spec adjunct | erase/insert により同じ A/raw member を local に移す。wrapper を消費し、raw value を消費して fresh slot value を作る。旧 graph の erase は起きない |
| rich移転 | current raw の accepted `Has(storage)`、fresh slot **ghost ClaimId**。fresh handle は current slot の存在を仮定しない | accepted `RawIntoSlot` を計算された `consumeOne` へ構成。既存 `into_slot_step_of_raw` / `empty_claim_conversion_preserves_flat` で全 Accounting 義務と rich WF を導出 |
| refinement | `RefinesSlot.issuance` は historical issuer birth certificate。current storage authority ではない。current authority は `packet`, `frame`, `active` のみ | source current graph、original A origin、旧 raw frame、phaseに応じた一個の current raw/slot と exact active inventory を対応付ける。計算されたslot POST全体との等式や post-WF を relation の仮定にしない |
| 物理保持 | issuerで生成した geometry/world を conversion 時には更新しない | `flat`・scope・bytes・access・placement・semantic state が固定。accepted footprint conservation と旧 claim preservation を証明 |
| None | trusted issuer の caller-visible failure/refund 契約 | accepted None event は source/geometry/rich/interpretation 全 identity。`Dispatch` に None constructor はなく、destructure/into_slot successor へ到達しない |

`RefinesSlot` は birth ledger と current ledger を区別する。consumeOne の inactive raw table entry が残っても current authority ではない。source `consumedValues` は wrapper/raw VALUE の消費であり、F53 の temporary PLACEMENT 消費とは別である。

original Allocation は accepted rich に first-class A constructor がないため source adjunct inventory と固定 interpretation で表す。A identity preservation を accepted F0 typed package transfer と呼ばない。新しい source carrier graph は actual AST / checker derivation ではない。source slot value serial はこの単一 successor の新規値を表すだけで、後続の一般的 value allocator / control-flow join は扱わない。

## 構成的証明と非空 frame

- `OneBackingSlotSource`: `start` は F53 `somePost.current` を直接 liftする。`matchPost` は Some wrapper と OneBacking→Some placement を eraseし、同じ bundleをlocalへ移す。`destructurePost` は bundleと二つのmember placementをeraseし、**同じ original A + full raw**を別localへ移す。`slotPost` は raw currentをeraseし、空slot currentをinsertする。各個別 `Step` の SourceWF を導出。
- `OneBackingSlotRich`: `start_refines` → `match_refines` → `destructure_refines` → `construct_raw_into_slot` / `slot_refines`。`some_post_to_slot` は許可された F53 Some POST から、`issuer_to_slot` は issuer PRE supply から全経路を証明する。
- `new_raw_not_frame`: 新しいclaimと旧claimが同じhandleならHasからregionが一致し、historical lineage injectivityとsource fresh serialに矛盾する。旧claim保持を fresh R/handle の独立仮定で埋めていない。
- `original_allocation_and_full_range`, `original_A_available`: original source A valueとslot extentのrich regionが一致し、offset 0、length sizeofH、capacity exact。A localはAVAILABLEのまま。
- `exactly_one_current_slot`, `unique_full_slot_claim`: source graphで唯一のslot value、accepted Accountingで同じfull extentを覆う第二slot claimの排除。
- `no_early_typed_authority`: F0 empty / placement none / source extras empty。typed H root、D、ptr、loan、incarnationの生成はない。

具体例は accepted F53 `concrete_some_simulation` を再利用する：old source R serial40 / rich R_C=0 / A_C value1000 / claim0を保持し、new serial41 / rich R_B=7 / A_B value1004 / raw value1005 / claim9を発行する。Some value1007を消費、OneBacking value1006を消費、raw value1005を消費してslot value1008 / claim10へ移す。current rich activeは**{10,0}**、claim9はinactive。source currentはA_B local1004とslot local1008にold C graphをframeしたもの。old CのSome/member placementは正当な旧current frameとして残り、new Bの消費済みwrapperとは区別する。24 bytes / align8はillustrative target入力でありnative ABI測定ではない。

## 独立した攻撃 controls

`Counterexample/OneBackingSlot` は正当な構成例を実際に改変し、accepted 3+1 controlも再利用する。

| 攻撃 | 正確な拒否・境界 |
|---|---|
| A_Bをold A_C value1000へ置換 | source allocation identity。rich WFだけでは検出しない |
| original A_Bをcurrent graphから紛失 | source exact current inventory |
| A_B interpretationをold R_Cへ置換 | issuer-derived Allocation origin equation |
| source rawを23 bytesへ短縮 | full descriptor identity |
| rich raw rangeを23 bytesでNode24へ変換 | accepted RawIntoSlot exactSize（POSTに依存しない） |
| accepted 3+1をONE full storageとしてslotへ | accepted rich WF/RawSplitは成立するが、full Hasを持つactive handleがない |
| same valueのslot carrier複製 | source UniqueCurrent |
| distinct rich handleに同じfull slotを複製 | accepted NoOverlap。集合のcoverage成立だけでは不十分 |
| new slotとold rawを同時current化 | source exact current graph |
| 消費済みOneBackingをcurrentへ戻す | source exact current graph |
| source slotをretired serial0へ置換 | source region identity |
| original issuer Rをretired rich R200で再発行 | inherited accepted live-fresh-but-history-stale countermodel |
| current slot extentをretired rich R200へ改変 | accepted Accounting.inScope |
| source Hをotherへ改変/要求 | source descriptor typeとclosed Node admission |
| richでsame-size other TypeIdを使用 | **RawIntoSlotとrich WFは成立**。Node RefinesSlotは不成立。coreのサイズ検査をnominal identity証明と混同しない |
| Noneからsuccessorを作る | source Dispatch不能、旧A/raw保持、future A不在。内部refundはtrusted contract |
| slot POSTから同じ手続きを二重実行 | source phase前提が全constructorで不成立 |
| active raw自身のhandleをslot resultに再使用 | accepted resultFresh と sourceClaim.active が矛盾 |

不整合なaccepted core invariantは発見していない。same-size other Hはcore conflictではなく、Node nominal mappingを外部型解釈に残す正確な境界である。

## 検証・監査・停止

新規四moduleの **117 explicit declarations / 61 theorems**（source48/21、rich24/15、witness14/6、controls31/19）を全て既存 `#print axioms` auditへ追加した。controlsの19 theoremには18 refusal/boundary checksとsame-size other Hのpositive core controlを含む。generated constructor等はそれらの宣言と使用する定理のtransitive auditで検査される。audit logic/allowlistは変更しない。custom axiom / proof placeholderゼロ、standard Lean logicのみ。

`lake build` は **810 jobs SUCCESS**、`scripts/check-proofs.sh` は **2024 axiom reports SUCCESS**（baseline1907 + new117）。全新規宣言の明示audit一覧は `scripts/check-proofs.sh` の Issue #55 block。exact candidate head / treeとGitHub Actionsのexact-head結果はDRAFT PRとIssue #55の一回のTrack F報告へ記録する。

今回のTaskは3–4 substantive hours上限のresumptionとして実施し、usage-limitの停止時間は実作業時間に算入しない。最初の成立境界はこのslot bridgeであり、残りの作業は同範囲のnegative controlsとaudit/publicationのみ。Domain optional stageは実施しない。

Domain発行、initialize、borrow、destroy、deallocate、original A解放後のterminal、Tree A/B間の関数間責任移転、cJSON five-root、0..5 allocation failure、6+4+2 Change/Reset、general allocator/generic/FFI/ABI、native allocator/compiler checker、C17、S1、North Starはこの成果の証明対象外。H1 DIRECT AUTHOREDはSTOP/UNDECIDED。DRAFT PRを未mergeで残し、Issueを閉じず、自己merge・canonical変更・Compiler実装・他Track起動をせず停止する。

F ONEBACKING INTO-SLOT REFINEMENT: BOUNDED SOURCE→RICH CUSTODY PROVED, NOT COMPILER-VERIFIED
