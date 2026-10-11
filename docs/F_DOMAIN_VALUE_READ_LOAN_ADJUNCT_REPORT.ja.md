# F #59 — 型付きroot開始前のDomain-value read loan限定adjunct

Track: F。NewLangの既存LifetimeDomain意味論と所有値管理の形式検証。

**F DOMAIN-VALUE LEXICAL LOAN: BOUNDED ADJUNCT INTERFACE PROVED, NOT SELECTED CORE**

新しいproof-only adjunctを**1 moduleだけ**構成した。F57の実際の発行POSTから、original Domain valueを保持した単一ordinary read loanを取得し、unit normal bodyの境界検査後に終了できる。新しいscope/token/guardは明示したモデル抽象であり、accepted coreの既存acquisitionでloanが得られたとは主張しない。selected-coreへの接続には下記interfaceが残る。矛盾やCompiler/native correctnessの証明ではない。

## 固定authority・source rule・既存の型の違い

- FormalProof/main `e2e540a4a6bfd23c6a5ba30fc19039e7a3323b0c`。F55/PR56、F57/PR58のaccepted adjunctを無変更で使用。独立branch `f59-domain-value-read-loan`はこのexact mainから開始。
- Compiler/main `a5343bf70004b30a8b026e52aa2fde93b5920be0`。API commit diffは開発プロセスJP/ENの§4.1.1追加だけ。CURRENT_SPEC、Draft17.30、Design Decision Procedure、Design-Intent Ledgerは親`b75…`と同じblobであることも確認。
- CURRENT_SPECはDraft17.30。Draft17.31 / DI-015は未採用・merge HOLD。Compiler実装・canonical変更を行わない。
- §11 ordinary `ref<read,T>`は**Copy + Discardable**だがscope-bound。§13.1 Domain VALUEはnonCopy/nonDiscardable。ref copyは同じscope依存を保持し、新しいDomain ownershipやloan grantではない。
- §13.3 ordinary ref to the exact Dはstability evidence。§13.7はcurrent lexical localのconsume/transfer/destroy conflictを禁止。§14.5–14.6はvalue transfer/finalizationとlive Domain-dependent capabilityのconflictを区別する。
- §13.8 bodyはexactly-once lexical block。resultだけでなくsurviving current valuesもending scopeと照合し、依存を消さずにloan終了後へforwardする。final unified surfaceは固定しない。

accepted F0 `AcquireRef`は`PtrToken`から**live object root**を要求する。F1 `FieldAcquireRef`もlive structural root/fieldを要求する。Domain carrierはroot location/incarnationではない。F2はloop iteration bindingsとfinite exit dependenciesのモデルであり、Domain-value read-loan acquisitionそのものは存在しない。

このadjunctの`Token {domain,value,scope}`はroot/ptr/incarnationを持たない。ordinary read capabilityを新たな値管理層へ明示的に登録する。F57 source inventoryの`extras`は従来のprojectionのまま保持し、新tokenは別のadjunct registryに置く。これを「新tokenも存在しない」と読み替えない。

## 最小の構成的定理

実装・全宣言は[DomainValueReadLoan.lean](../NewLang/Adjunct/DomainValueReadLoan.lean)。

`Begin`のPREは、source WF、single-call ready phase、選択した**original D/valueがavailable**であること、ordinaryRead modeだけ。token_eqはcomputed `makeToken`、POSTはcomputed `beginPost`。scope idはhistory counterからfreshに計算する。PREへcurrent tokenやloan certificateを置かない。

- `acquisition_constructed`：Begin、POST WF、current token、scope freshness、source inventory完全同一を同時に導出。
- `current_preserves_original_available` / `original_nonCopy_domain_still_unique`：loan中もoriginal D/valueがavailableで唯一。借りることによってDをconsume/duplicateしない。
- `active_blocks_original_consume`：exact borrowed DはUnborrowedでなく、CanConsumeが不成立。
- `active_blocks_guarded_core_permissions`：この**新しいsource guardを明示してF0の外部permission Propへ渡した場合**、RawDomainTransfer / RawFinalizeDomainの前提が不成立。実際のending transitionはモデル化しない。
- `end_preserves_output_and_owner_obligations`：checked EndからPOST WF、original source/owner責任完全同一、scope history保持、unchanged output/deps、post-surviving valuesの有効性、全old tokenの失効を導出。
- `end_preserves_nonDiscardable_exit_obligations`：loanを閉じてもA/slot/Dのnormal-function-exit義務は消えない。loan endはDomain consumeやfinalizationではない。

Endのチェックはcurrent exact token、body evaluation count=1、body resultと全survivorsのvalidity、F2.ScopeClosed、computed POST、output=元のboundaryである。countはこのadjunctの**明示source義務**であり、既存parser/evaluatorがexactly onceを実装した証明ではない。具体的成功witnessはunit body / no surviving refs / no owner-state mutationの一回だけ。

finite `Value`はunit/stable-token/pairに限定し、再帰的にdepsをunionする。内側pairやordinary refのコピーを経てもscope依存が残る。`Boundary`はresultとsurviving current-value listを同時に調べる。任意AST、cyclic memory、closure/call effectやunknown依存を空集合に置換するモデルではない。それらはこの有限profileの外であり、実際のsource loweringとの完全対応は未証明。

## accepted rich / F2との接続と、残るexact interface

`Refines`は新Loan WFとF57のactual `RefinesDomain`を保持する。checked Begin/Endは**rich全状態を変更しないstuttering projection**で、元のDomain live/carrier、physical、ledger、Accounting、Geometry、A/slot/old Cを保持する。POST rich WFを仮定して新状態の正しさを隠さない。具体的witnessのrich WFはF57 `complete_issue`から得る。

`current_has_actual_live_domain_and_carrier`と`current_token_dependencies`により、new tokenが示すexact D/valueはactual F0 liveDomains/domainValueCarrierに対応し、DomainLive dependencyは本物のlive factである。

`scopeTag`はfresh adjunct scopeをF2.Dependency.iterationへ**明示的に符号化**し、既存の純粋なScopeClosed checkerを再利用する。この符号化は、enclosing loop/別loan scopeを含まないsingle-loan profile専用である。F2 loop entry/Return/Continue操作をDomain loanへ読み替えず、iteration bindingとruntime loan scopeの同一性やglobal registryのdisjointnessを証明したとは主張しない。

最も重要な検査は`witness_guard_is_not_a_rich_only_fact`：entryとactive-loanは同じsource inventory / rich projectionを持つのに、CanConsumeはentryで成立しloan中は不成立。**rich WF・live D・carrier mapだけではloan permissionを復元できない。** 新registryを実際のsource-current-value guardへ接続する必要がある。

`still_no_selected_object_ref` / `witness_selected_core_bridge_still_missing`はnew current tokenがあってもaccepted AcquireRefが成立しないことを保持する。typed rootを架空に作って解決しない。

selected-coreへ進むために未証明なのは：

1. `available original Domain value/binding + fresh lexical scope → ordinary Domain-value scoped ref`という独立acquisition signatureとselected scope/ref history。
2. 実際のlocal type/current-value解釈、implicit local lifetime、Domain carrierとの対応、Copy ref派生/消滅の追跡。このadjunctのOperand分類がcompiler AST/checkerと同じだという証明。
3. 全source consume/transfer/finalize/exclusive applicabilityがnew active-loan registryをconsultするという接続。今回のguard-fitting theoremをaccepted core単独のpermission theoremとみなせない。
4. 実際のbody評価のexactly-once性と、全result/surviving memoryのtransitive dependencies、一般的なscope namespaceのsound embedding。

## original witnessと境界条件

`witnessEntry`はF57 computed POSTを使用。D=1 / original value1009、A_B1004、empty slot1008、consumed raw、R_B7/current slot claim10。old raw-only C/claim0を保持し、rich active claimsは**{10,0}**。retired D0/source namesはF57 history、retired scope0は別のexplicit scope history。fresh loan scope1はこれらの番号やBackingRegion/addressからauthorityを推論せず発行する。

`witness_acquisition`→`witness_end`→`witness_round_trip_nonempty_frame`は一回のloan grantとdischargeを構成。actual rich WF/Accounting、original A/slot/current Dは保持。全occupancy vacant、incarnation history空のまま。loan close後もoriginal Dがavailableであり、unit function resultへD責任を捨てるNormalExitは拒否。

| 検査 | Leanで確認した範囲 |
|---|---|
| retired D0 / wrong current Domain value1010 | Beginのcurrent available前提が不成立 |
| Copy pointer operandをDomain localとして渡す | explicit RequestBegin分類が拒否。実際のAST分類の証明ではない |
| pregrant/retired scope/closed token | Currentが不成立 |
| Domain duplicate1010 | original source Domain唯一性が拒否 |
| independent duplicate grant/nested second grant | single-loan ready phase guardが拒否。canonical一般のordinary nested loansを禁止しない |
| ordinary refを同scope内でcopy | **許可**。same token/depsを保持。Domain複製とは区別 |
| exclusiveをordinary readとして取得 | mode guardが拒否。active borrowed DのUnborrowedも不成立 |
| Dをactive loan中にmove | F57 source WFだけならforward POSTは可能だが、新Loan WFのavailable-current整合が拒否 |
| active Dのconsume/finalize permission | new explicit guardをF0 permissionに渡した場合に拒否。finalize transitionは実施しない |
| result / nested copied result / stored survivorへref escape | recursively computed scope depsがScopeClosedに反する |
| double close / omitted close / body count≠1 | exact current/Complete/once guardが拒否 |
| wrong Domain stability evidence | EvidenceForのexact D一致が拒否。initialize適用は対象外 |
| A/slot紛失 | inherited source owner invariantが拒否 |
| pre-initialize typed root/ptr/incarnation | new Tokenに存在せず、actual rich vacancy/historyを保持。typed operationは実施しない |

## trusted境界・historical audit・実証・停止

**新しいモデル抽象**：scope history/registry、current nonowning Token、typed Operand分類、finite Value/Boundary表現、Unborrowedのguard fitting、exactly-once boundary count、unit-body frame restriction。これらは新しいproof-only definitions/guarded eventsとして検査する。実際のsource/core/ASTがこれらのguardと表現へ対応することは、未証明のモデル解釈上の前提である。

**既存のtrusted境界**：F55/F57 source authority/world/name interpretation、atomic issuer契約、Node typing/layoutと供給。custom logical axiomsや未完了proofは加えない。**証明済み**：このadjunctのcomputed acquisition/end、WFとcurrent identity/nonCopy owner保存、finite escapeチェック、actual rich frame保存とF0 DomainLive対応。**未証明**：上記selected-core interface、Compiler/native/ABI/FFI/general loan/unknown body、later typed lifetime start。

Process §4.1.1・§4.2、Design Decision Procedure Gates A–Cを確認。Historical design audit：**N/A — faithful investigation of existing Draft17.30 §§11/13.7–13.8/14.5–14.6; proof representation only; no language rule changed**。DI009のA/Storage/slot/D separation、DI010のscoped mode-preserving refs、DI011–014のknown-call/LiveTail/custody/5-root boundariesはKEEP。final unified syntax/DI006、general scope/call graph/full H1はDEFER。旧Surface Draft1/1_1はexperimental evidenceでありnormativeに昇格しない。ledger修正は不要。旧M9チャット全文は網羅調査していない。

単一新module **86 explicit declarations / 48 theorems**。全宣言は既存`scripts/check-proofs.sh`へ1回ずつ追記し、audit logic/allowlistを変更しない。ローカル`lake build`は**815 jobs SUCCESS**、auditは**2194 theorem axiom reports SUCCESS**（standard Lean logicのみ）。accepted F0/F1/F2、F55/F57 adjunct、canonicalは無変更。exact candidate headとGitHub Actionsの実測はDRAFT PR / Issue #59の最終報告に記録する。

2026-10-11 13:09 JST開始、2–4h上限のbounded task。単一unit-body loanとdischarge/negative controlsで構成を終了し、以後は監査・公開・報告のみ。initialize、typed root、ptr取得、field updates、destroy/finalize/deallocate、5-root/native/general bodyへ進めない。Issue報告後直ちに停止し、自己merge/close・他Track起動を行わない。
