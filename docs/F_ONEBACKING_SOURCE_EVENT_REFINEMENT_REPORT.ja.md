# F #53 — one original OneBacking issuer の限定的な構成的 refinement

結論：選択済み trusted builtin の atomic Some/None 契約を source event として形式化すると、発行済み A/raw/Some を PRE に置かずに、Some の post World・Geometry・scope・full storage claim・original Allocation interpretation を構成できた。accepted rich `WellFormed` と source current-ownership の双方を導出した。これは **source-spec simulation と rich post-state construction の候補**であり、Compiler / C / native allocator の実装正当性の証明ではない。

## 固定 authority と範囲

- FormalProof base: `7b760f64d5fdceb9753df52d2362fbf43c6edbad`。F #49/#51 の補助証拠を含む固定 main から独立 branch を開始。
- Compiler authority: `b75baea96a644e68634baee383299b66981b3c62`、`CURRENT_SPEC.md` が指す canonical Draft 17.30 §§3.1–3.4。
- 正式な引用箇所は §3.2 の **`### Draft 17.24 bounded allocated recursive root source profile`**、[四つの発行条項](https://github.com/wakairo/NewLang_Compiler/blob/b75baea96a644e68634baee383299b66981b3c62/docs/reference/NewLang_v0_spec_Draft17_30.md#L1746)。架空の literal §3.2a は引用しない。
- [M #287 proposal](https://github.com/wakairo/NewLang_Compiler/issues/287#issuecomment-6097057299) と [Coordination research acceptance](https://github.com/wakairo/NewLang_Compiler/issues/287#issuecomment-6097078356) は nonbinding / unselected。提案を canonical law に昇格させていない。
- 一個の closed completed Node H、一回の issuer event、PRE の grant は最大一個、Some/None の二結果。具体的 PRE は一個の **raw-only R_C** とその A/raw/Some ownership を持つ。rich constructor 自体の frame lemma は任意の PRE rich WF を扱うが、source profile を一般化しない。

## PRE と POST の provenance

| 項目 | PRE / 信頼境界 | POST / 実際に導出したもの |
|---|---|---|
| H / layout | `ClosedH.node` のみ。`Target.sizeofH > 0`, `alignofH > 0` は選択済み compiler/target layout 入力。実際の declaration resolution・ABI layout 証明はない | `Supply.n = Target.sizeofH` により exact positive full range を構成 |
| 成功環境 | aligned address **observation**、一つの fresh rich R、n 個の disjoint abstract bytes の supply、injective byte coordinates。fresh ClaimId は proof context の handle | 新しい Geometry / compatible World / RW access / live R / scope / storage を constructor で追加 |
| 歴史 | old source lineage counter と interpretation の used-R history、供給 R は history 外 | source serial を生成し、interpretation を更新。live freshness と historical freshness を別々に検査 |
| 既存状態 | `SourceWF`, accepted rich `WellFormed`, generic `Refines`、PRE grant 数 ≤ 1 | 全 old R の bytes/access/geometry と active claim、old source carrier / A origin / raw claim の identity を保持 |
| original A / raw / wrappers | **新しい A, raw source value, full Has, current Some, Matched, D/ptr/root は PRE にない**。`pre_has_no_future_allocation_or_carrier` で future A/carrier の不在も導出 | fresh serial の a/raw → OneBacking member → Some member/result。opaque A origin と raw claim の interpretation を構成 |
| None | trusted builtin の失敗境界は caller-visible resource を公開しない。内部 platform refund は契約であり実装証明ではない | source / geometry / rich / interpretation の全 identity。新しい original A/Some/R/scope/claim なし |

address observation と abstract byte supply を native memory に結ぶ正当性は trusted platform/target 境界に残る。数値アドレスから semantic R を計算したり、ghost disjointness を native allocator の検証結果と呼んだりしない。RW Bool の発行も選択済み builtin の grant を表し、ハードウェア access 検証ではない。

## 形式化と非循環性

`OneBackingIssuerRich.lean` は accepted `World`, `Geometry`, `PhysicalState`, `Ledger` を直接用いる新しい **adjunct introduction infrastructure**。既存 rich transition に fresh issuance があるとは主張しない。

- `constructive_wellFormed`: PRE rich WF と Supply から、extended scope を持つ POST の accepted `Accounting` / `WellFormed` を証明。roots・placements・typed claims が old frame にある場合も保持する。new claim は storage のみ。
- `compatible`, `regions_disjoint`, `old_world_frame`, `old_claim_frame`, `exact_fresh_byte_count`, `exact_range_and_RW`, `exactly_one_full_new_claim`: geometry/world の整合、byte conservation、one full current claim を導出。
- 使用する accepted 義務は `AccountingShape` の全九項、`NoOverlap`, coverage、既存 F0 WF。duplicate/full-claim 排除には `nonempty_claim_cannot_be_covered_twice` を使用する。F0/F1 定義・定理・WF を変更していない。

`OneBackingIssuerSource.lean` は atomic trusted source `Step` と joint `IssuerEvent` を定義する。Some は環境入力と old WF/bound だけを受け、POST state/interpretation を計算する。None は四つの view を保持する。

- `pack` / `wrap` は **以前の temporary placement を erase** し、同じ a/raw value ID を member へ移す。`some_event_has_actual_move_trace` と `moves_consume_temporaries` が二段の移転と consumed placement を示す。binding の消費を a/raw 自体の破棄とは扱わない。
- `Refines(src,g,rich,i)` は任意の inventory の relation。historical lineage injectivity、original A origin、**A inventory の iff**、raw claim / exact capacity、live/scope/claim inventory、current graph を対応付ける。POST equality、post WF、allocator success を relation 内に隠していない。
- `some_post_refines` / `some_simulation` / `every_issuer_event_refines` は計算された POST が Refines と accepted rich WF を満たすことを証明する。
- `none_simulation` / `every_none_event_is_full_identity` は None の caller-visible identity を証明する。
- `new_allocation_has_exactly_one_current_carrier`, `one_original_allocation_per_R` は original A の source 非Copy ownership。一方、accepted accounting は raw **byte** ownership を証明する。この二者を混同しない。
- `success_has_no_early_authority` は source typed root / D / pointer / loan / incarnation の不在、rich F0 empty と no placement の保持を示す。raw-only source interpretation の範囲内であり、既存 rich typed root の移転証明ではない。

original Allocation は accepted rich 内に既存の first-class A constructor がないため、**新しい source adjunct inventory と interpretation で表現**する。その current-ownership 証明を accepted F0 typed package theorem と呼ばない。新しい typed initialization / domain issuance interface は作っていない。

## 非空 witness と実際の改変 controls

`OneBackingIssuerWitness.lean`: old source serial 40 / rich R_C=0 / original A value 1000 / raw claim 0 から、fresh source serial 41 / rich R_B=7 / original A value 1004 / raw claim 9 を構成。既存 C と B の二つの independent owner chain が残り、scope/live/claim の exact set と old frame を証明。24-byte / align-8 は **illustrative target input** であり C sizeof の測定値・ABI 証明ではない。

retired source serial 0 の rich R=200 は used history にあり live ではない。retired address observation 4096 を新しい成功でも用いる例を示し、new semantic R=7 と retired R=200 は別と証明した。二つの live allocation が同じ native memory を共有して安全、という例ではない。

`Counterexample/OneBackingIssuer.lean` の **14 theorem controls** は、構成した正当な状態または accepted RawSplit を実際に改変・使用する。

| 攻撃 | 拒否する実際の条件 |
|---|---|
| A_B の別 available carrier | source current uniqueness。rich byte WF はそのまま成立 |
| A_B の紛失 | source current inventory completeness。rich byte WF はそのまま成立 |
| old A_C value ID を B member に移植 | old/new current carrier conflict |
| 別 value ID で同じ original R を clone | source original-region uniqueness |
| A_C の origin を A_B interpretation に使用 | source-to-rich Allocation origin equation |
| original raw_B の二重・重複 full claim | accepted `NoOverlap` / nonempty-claim exclusion |
| n−1 raw | generic fullRaw refinement と実際の accepted coverage の双方。last byte 123 が失われる |
| accepted 3+1 を ONE full raw と呼ぶ | accepted RawSplit / rich WF は成立するが、full Has を持つ active ID が存在しない |
| retired semantic R=200 を再発行 | live-fresh Supply は作れるが lineage/history refinement が拒否 |
| None に ghost Allocation | exact A inventory の iff |
| None に Some / backing / scope / claim | joint None event の full identity |
| early typed root / D | source `noEarly`; fabricated live D は accepted F0 domain-carrier coherence でも拒否 |

## 検証・分類・停止範囲

- 新規 adjunct 四 module、**115 explicit declarations / 60 theorems** を全て `#print axioms` の既存 audit に追加。既存 audit logic / allowlist は変更しない。
- `lake build`: **806 jobs**。`scripts/check-proofs.sh`: **1907 reports**、standard `propext / Classical.choice / Quot.sound` のみ。project 内の custom axiom / sorry / admit はゼロ。
- exact candidate head と exact-head CI run は、draft PR と Issue #53 の Track F report に記録する。
- **source-spec simulation**: stipulated atomic trusted builtin からの source event / ownership / None identity。
- **accepted-rich construction**: POST World/Geometry/scope/Accounting/WellFormed と byte uniqueness。
- **conditional boundary**: selected completed H の resolution と target sizeof/align、supplied abstract bytes と native memory の対応、platform access、failure refund。
- **production evidence**: F #51 の read-only P278 frozen head `4bc6b690e87b4646596dfd460bea26e9a5d8dac5` / 13 controls を既存 empirical evidence として保持。新しい native / compiler correctness theorem はない。

歴史 Process §4.2 / Design Decision Procedure は、選択済み四条項の忠実な FormalProof adjunct だけを追加するため **N/A**。DI-009 の old success-only allocator entrance は superseded、distinct R/A/raw/full cleanup は KEEP、DI-008 address observation / DI-010 loans / DI-011 known calls / DI-012 LiveTail / DI-013 custody / DI-014 five-root は変更しない。DI-015 / Draft17.31 は unselected。legacy M9 全項の適合性を証明したとはしない。

境界成立により STOP。into_slot、fresh domain、typed initialize、mixed packet return、after-A terminal、0..5 multi-branch、6+4+2 Changes、native C17、general allocator/FFI/ABI、S1、North Star は DEFER。Compiler PR #273 head `f778eba116d1834cc79c0bef6f6c17051102049f` は DRAFT UNMERGED / Gate E HOLD、P #285/#286 は独立、Compiler #268 は OPEN、full original B native STOP、H1 PASS/FAIL UNDECIDED。自己merge・canonical編集・Compiler実装・他Track起動は行わない。

F ONEBACKING ISSUER REFINEMENT: BOUNDED SOURCE-EVENT/RICH CONSTRUCTIVE CANDIDATE — PRE/POST PROVED, NOT COMPILER-VERIFIED
