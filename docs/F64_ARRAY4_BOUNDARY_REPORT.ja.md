# F64 — one-root/four-fixed-child boundary investigation

Track: F. NewLang言語意味論・形式モデルの品質検証。判定: **MODEL INCOMPLETE HOLD**。

## 固定authorityと研究範囲

- FormalProof/main: `5437f92d099e228773d31e2323e8ee6228ca21bf` (tree `33e159b672c0254cdd85dd23b4813f4d2c75b12f`)。
- Compiler/main: `c6ae58512683090b2d98b09f51765143b1517345`。
- Canonical: CURRENT_SPECが指すDraft17.30。参照Draft blob: `db8fe08f811acc8286f2d37e9d3229b5d7a67067`。
- 比較候補: Compiler DRAFT [PR533](https://github.com/wakairo/NewLang_Compiler/pull/533)、固定head `817a5534b131b9b70b5d37f78a4bad1e39ee4ad4`、full Draft17.32冒頭§17.32.1–4。未採用。Draft17.31/DI-015も未採用。
- 指示: [Issue64](https://github.com/wakairo/NewLang_FormalProof/issues/64)。
- Compass、Product Value Strategy §§1.1–1.2、[C532](https://github.com/wakairo/NewLang_Compiler/issues/532)、[V528](https://github.com/wakairo/NewLang_Compiler/issues/528)、開発プロセス §§4.1.1/4.2/4.3.1、Design Decision Procedure、F README/F1.3/F1.4/F3のscopeを確認した。
- Historical design audit: **N/A — proof-only finite diagnostics; no language/source/API/semantic selection**。Draft17.30 §§3.1–3.5/11/13/25/26をKEEP。DI-001/007/008等の既存意味論を置換せず、DI-002/005/006とArray4候補採用はDEFER。旧実験やLedgerをnormative authorityへ昇格しない。

読み取り専用mapping: **2026-10-16 22:42:20–23:08:14 JST（25分54秒）**。この間はrepositoryを変更せず、既存定義の読み取りとstdin上のLean probeのみ。既存証明・仕様・pins・workflowは変更しない。

## 最初の不足interface

Canonical §25.1は1つのArray root、順序付きcontiguous要素、stride `sizeof(T)` を要求する。§25.2のref projectionは親と同じmodeで親scopeに依存する。ptr projectionはdanglingでもlocationを表現できるが、新rootやderef authorityを発行しない。§26.4のCopy/Discardableは全possible payload typeから静的に決まり、§26.5はNone表現をopaqueとする。NoneにSome occurrenceはなく、将来のSome payloadも独立rootではない。

候補Draft17.32は、この意味論に従う1つのlexical `Array<Option<u8>,4>{None x4}` source構築を提案する。4つの独立root、別nominal四field record、zero-fill None、`sizeof(u8)` strideへの置換を認めない。候補自体もindex/ref/ptr projectionをsource-admitしていない。今回の数学的検査は、そのsource admissionや公開owned証拠の実装証明ではない。

最初の不足は、**1つのtyped Arrayの元rootと4つのtyped current Option None subplacesを、親refのmode/scopeおよび親placementから導く固定subobject refinement**である。対応するacceptedな型・関係はまだなく、既存の各層を並べただけでは導出できない。

| 既存のexact definition | 表現する範囲 / 未接続部分 |
| --- | --- |
| `F1.StructuralLayout`, `TreeWellFormed` | finite PlaceId/pathの木。pathはsemantic sequenceでありbyte offset/Compiler ProjectionId発行証拠ではない |
| `F1.StructuredRoot` / `CurrentState` | root単位のgoverning Domainとfixed nodeのincarnation/currentFact/deps。installed contentはopaque NatでArray/Option current variant解釈がない |
| `F1.Reference.FieldAcquireRef (stable access : Prop) s ptr d` | current親・子・path・incarnation・governingを検査するpoint predicate。typed backing/permissionは外部Prop。結果refのmode/scope/extentは存在しない |
| `Backing.PhysicalState.placement : RootLocationId → Option Placement` | **root** extentのみ。fixed-child extentやpath→layout derivationはない |
| `Backing.EvidenceValid w e` | AccessLe(e.access, World.access)。親から借りたrefのAccessとの比較ではない |
| `Occupancy.Accounting` | scoped backingのpositive exact root/raw/slot責任。scopeはaccounting region範囲で、lexical scopeでもAllocation/deallocation値でもない |
| `Conditional.State` / `erase` | root-level sum。eraseは各sum rootをsingleton fixed layoutにするため4つのembedded Optionには直結しない |
| `F3.Memory.SumLifetime` | one-root/one-claim sum lifetime adapter。arbitrary fixed/nested sum layoutを含まない |
| `F2.ScopeClosed` | loop iteration dependencyの境界。一般の親子ref scope issuerではない |

注意: `F1.Conditional.Allocation` はfresh ValueFactId/OccurrenceIdの証明用割当recordであり、canonicalの非Copy **Allocation値ではない**。F1.3 placementやF1.4 root claimもその値を発行・解釈しない。lexical Arrayにheap deallocation用Allocationを新設して不足を埋めてはならない。既存のsource inventory adjunctをこのArrayへ接続するissuerも仮定しなかった。

必要な接続の内容は「sourceのexact Array/Option型と4つのNone facts → 同じ元R/Dと親layout内のchild extent、parent-bounded mode/scope、元の責任inventory保存」である。これは**未実装の義務の記述**であって、新しいLean仮定を置いて証明したtheoremではない。

## 限定Lean証拠

追加は `NewLang/Adjunct/Array4Boundary.lean` 1つ。既存定義を変更せず、finite fixturesと既存定理のspecializationだけを保存する。これは**preinitialized abstract F1 tree**であり、actual source、typed None、real first-class Allocation/Domainの発行を証明しない。

- `tree` / `state_wf` / `exact_places` / `child_distinct` / `child_parent` / `child_role`: 元のmodeled rootを1つ、root-relative childを4つ構成し、全childがdistinct fixed subplaceであることを証明する。metadata上のDomainは1つだけ。child別のgoverning/occupancy recordは作らない。
- `physical_wf`: 同じlive-root supportに対する1つのroot placementを構成。Worldのnominal backing・extent・root separationを実際に検査する。ただしfixed-childのtyped physical derivationやfull Accountingとの合成は未証明。
- `point_acquisition`: current field tokenの取得条件を、**外から実際に与えられたstable/access Propを残したまま**specializeする。raw Copy tokenだけからauthorityを作らない。
- `concrete_end_step` / `ended_wf` / `concrete_end_invalidates_all`: concrete non-vacuous F1 EndStepとpost WFを構成し、4つ全てのold field acquisitionが失敗することを証明する。fixtureのending authorityとDiscardableは明示的に設定したもので、source Array終了の静的型検査から導いたものではない。physical destroy/deallocateやDomain finalizeまでの合成はしない。
- `restarted_rejects_all`: accepted `FreshTreeRestart`証明が**与えられた場合に限り**古いchild tokenは復活しない。restart/initialize issuerは作らない。

### 独立した拒否例

1. `duplicate_projection_rejected`: distinct child 0/1に同一semantic pathを割り当てたlayoutはTreeWellFormedではない。`misparented_token_rejected`: childを親root placeとして偽装したtokenを拒否する。
2. `concrete_end_invalidates_all`: concrete親終了後、全4childがstale。fresh restartについても上記の条件付き証明がある。

追加controls: `wrong_site_rejected`、`wrong_domain_rejected`、`child_is_not_erased_root`、access/stabilityのないCopy tokenの拒否。`overlapping_extra_root_rejected`は親の占有byteと重なる別root placementをaccepted rootsDisjointが拒否する。既存F1.3の `equal_hypothetical_addresses_do_not_identify_regions` も確認した。numeric label一致はnominal identity/governing/currentnessの検査を置換しない。

これらは数学的な拒否証拠であり、Compiler public validatorの実装・拒否実測ではない。特に、上記のroot/domain metadata検査だけから、source上の非Copy Allocation値またはDomain値の複製不能まで証明したとはしない。

## HOLDを具体化する弱い推論の反例

- `world_bound_is_not_parent_bound` / `world_evidence_is_insufficient_for_parent_mode`: WorldがRW、親側evidenceがRO、別evidenceがRWの有限例。両evidenceはWorldに対しvalidで、semantic tree/physical root WFと**World evidenceだけを外部access Propとしたpoint predicate**も成立するが、RW ≤ ROはfalse。従ってF1.3のWorld上限を「親refからの非増幅」と読み替えられない。
- `guessed_extent_can_escape_by_one_stride` / `root_checks_do_not_constrain_guessed_child_extent`: abstract ordinal parent [0,8)、4th guess [6,8)、1 strideずらしたbad guess [8,10)、backing [0,10)。bad guessはbackingには収まるが親外であり、accepted semantic/root invariantsとは矛盾しない。child rangeが既存predicateの入力にないためである。
- `untyped_content_still_wf`: arbitrary installed-content functionへの置換後もCurrentWellFormedは成立する。これはNone/current variantをWFだけから推論できないことを示す。

**いずれもcanonicalの合法な不正操作のtraceではない。** 外部Propを弱めたり、モデルの外のguessを利用する操作を合法だと認めていない。scope/mode/layout/typed-None refinementの不足を具体化した診断であり、actual proved language contradictionではない。

8/10やstride2は有限診断のabstract ordinal数で、Optionのサイズ・tag・bit pattern・ABIではない。installed content91もNone表現ではない。zero-byte/tag、zero-fill、`sizeof(u8)`仮定を一切使わず、それが必要なrepresentation theoremにも進んでいない。将来Some(nonCopy)についてroot-level occurrence theoremは存在するが、このArrayのembedded Optionとのbridgeは未証明。

## 検証と停止

検証コマンド: `lake build`、`bash scripts/check-proofs.sh`。新規moduleの全explicit declarationを既存監査へ追加し、旧2278 entryの順序を保存する。受理済みF0/F1/F2/F3、canonical、Compiler、toolchain/lockfile、workflowは無変更。

ローカル実測: `lake build` **PASS (817 jobs)**。`scripts/check-proofs.sh` **PASS (2333 reports = 旧2278 + 新55)**。全55 explicit declarationsを監査し、標準Lean論理の `propext` / `Classical.choice` / `Quot.sound` のみ。新規custom assumptions、proof placeholders、unsafe declarationはない。旧監査順序保存と `git diff --check` も確認した。初期stdin probeの構文・elaboration修正は公開前の開発作業であり、最終moduleと全体監査は成功している。

測定結果と固定headのGitHub Actions URLはPR body / Issue64の一度のterminal reportへ記録する。初回自然CI cycleのみを利用し、結果目的のrerunは行わない。

§4.3.1の予測→実測→地図更新: 親EndRoot/semantic path検査は再利用できると予測し、その有限specializationは成立した。一方、typed child source/layout/refの接続が最初の不足と判明した。新しいissuerや一般projection機構へ拡大せず、CoordinationへHOLDとして戻す。

これはbounded FORMAL/EXPERIMENT evidenceであり、Array4 SOURCE/CHECK/public owned/C17/native証明、Ring safe API、Product GOではない。author+ordinary callerのL/R/P/V/C監査・再監査負担の縮小は未測定。比較対象のfactored C/Zig・同topologyのRust Option Ring（safeに構成できる可能性を含む）に対する優位も主張しない。次の探索方針・採用はCoordinationの裁定対象とし、他Trackを起動しない。

