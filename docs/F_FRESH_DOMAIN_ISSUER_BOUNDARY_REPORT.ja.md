# F #57 — fresh LifetimeDomain発行は構成、最初のDomain-value lexical loan bridgeはHOLD

結論：受理済みF55のoriginal A / exact empty slot / old raw-only C frameから、canonical `lifetime_domain()`の**fresh original Domain責任をsource-spec inventoryで構成**し、accepted F0 `liveDomains` / `domainValueCarrier`とrich `WellFormed`へ接続できた。Domain発行でbytes・claims・typed root・ptrは増えない。

**最初の未証明interfaceは、available Domain VALUEに対するlexical `loan_read`の取得・scope・permission・exit依存の接続。** accepted `AcquireRef`はlive OBJECT rootを要求し、このpre-typed entryにはそのrootがない。canonical loanが不正、あるいはcore contradictionという結論ではない。欠けたloan relationや安定性capabilityを新しく仮定して成功としない。

## 固定authorityと開始状態

- FormalProof/main `864c2d1ef9f0f0a61f79fa176944c59c549e30f6`、[F55/PR56の独立Coordination裁定](https://github.com/wakairo/NewLang_FormalProof/pull/56#issuecomment-6103116368)後。accepted F53/PR54、F55/PR56は無変更。
- Compiler/main `b75baea96a644e68634baee383299b66981b3c62`、CURRENT_SPEC canonical Draft17.30。実際の§3.2 heading `Draft 17.24 bounded allocated recursive root source profile`、§3.4、§§4/10/11/13/14を確認。
- Draft17.31 / DI-015 / PR273は未採用、MERGE HOLD。P294/P297/R296やexperimental PR295をoracleにしない。他Trackを起動しない。
- `FreshDomainWitness.before_refines`はF55 `complete_successor`の証明済みPOSTを使う。A_B source value1004、slot value1008、rich R_B=7 / slot claim10。raw value1005 / claim9は消費済み。R_C=0 / A_C value1000 / raw claim0とold graphは保持。
- PREにcurrent D、typed H root、ptr、stability refはない。fresh Dのcurrent carrierやready matched DはPREに置かない。

## 構成した最小の境界

`FreshDomainSource`はsource現在責任を`available`と`outgoing`の二placementに明示する。Domain identityとoriginal nonCopy valueは別の名前。`History`はretired domain/value名のみでcurrent権限を与えない。next Domainはhistory counter、next source valueはF55 graphの最大new valueを超える`packet.base+5`から構成する。

- `domain_and_value_fresh`: used historyの全Domain/valueはcounter未満、owner graphもnext value未満であることから、新しいDomain/valueがhistoryとA/slot/C graphにないことを導出。
- `issuePost`: 一回の選択済みatomic builtinがhistoryを延長し、**計算された一個の新D/valueをavailableへinsert**。owner/current slot/Rを変更しない。
- `issue_wellFormed` / `issue_derives_fresh_unique_available`: source Domain唯一性、value唯一性、available/resultのplacement disjointness、owner graphとの分離、消費済み値の再利用禁止を証明。unionの集合化で複製を隠さない。
- `Forward` / `forward_cannot_consume_twice`: scoped loanのないこのentryに限り、ordinary affine valueをlocalからnormal resultへ移す最小custody操作を検査。同じD/valueを二度consumeできない。Domain finalizationやknown-call applicabilityの証明ではない。
- `NormalExit`: A/slot owner record全体と全current Domain責任をresultへforwardする義務。Dを捨てたunit相当のresultは拒否。terminal cleanupを証明していない。

`FreshDomainRich.semanticIssue`は**新しいadjunct introduction**であり、既存coreにfresh issuer transitionがあったとは言わない。既存F0 Stateを使ってnew Dを`liveDomains`へinsertし、そのcurrent `DomainValueCarrierId`を構成する。occupancy/packages/facts/incarnationsは固定。`semantic_issue_wellFormed` / `rich_issue_wellFormed`は全F0 WFと既存rich Accountingを導出する。Backing world・Geometry・scope・ledger・coverageは固定である。

`RefinesDomain`はhistorical F55 slot certificate、current source inventoryとaccepted rich Domain/carrierのiff、non-domain frameを分離する。**D発行後のcurrent semantic stateをF55の`semanticEmpty`に偽装しない**。新しいDomain責任はfirst-class occupancy Claimとして表現されず、source inventoryとF0のlive/carrier viewで表現する。F0のcarrier map単独はnonCopy source placement、逆injectivity、歴史freshness、lexical permissionを保証しない。

`issue_simulation`はsourceとrichの計算されたPOSTからRefinesDomainとrich WFを導出する。POST state/ready D/current map/post WFはPRE仮定ではない。`forward_refines`はsource placement変更のcoarse rich projection保持だけを示し、call/loan許可とは区別する。

## 最初の正確な障害

`domain_value_has_no_accepted_object_ref`とwitness `lexical_domain_loan_first_bridge_unproved`は、real live D / current carrierがあっても、任意の`stable`, `access`, 数学的`PtrToken`に対してaccepted F0 `AcquireRef`を構成できないことを証明する。

必要なPRE targetは`∃ root, occupancy ptr.location = live root`。今回のproven POSTは**全occupancyがvacant**である。`DomainValueCarrierId`と`RootLocationId`をcast/同一視してtargetを作ることはしない。Domain値へのdirect lexical loanと、live Hへのptr→ref取得は別の操作である。

さらにF0 `RawDomainTransfer` / `RawFinalizeDomain`はscope-sensitive applicabilityを外部Propに残す。`UnvalidatedLoan`という外部の主張を置いても、それはaccepted loan/refではない。そのprojectionで`allowed=True`を選ぶとtransferとfinalizeは成立するnegative controlを証明した。**valid loan中の違法なtransfer/finalization traceを証明したわけではない**。これによりcurrent D/carrierだけを理由にpermissionをTrueへ置換できないことを示す。

F2の`ScopeClosed`は登録済みending-binding依存をrejectするが、DomainLive外部factだけはlexical scopeをprotectしない。新しいD値に対するref取得からそのscope dependencyを登録するaccepted operationがこのentryにはない。したがってref自身/result/surviving-stateのescape禁止を、現時点で成立済みと報告できない。

未証明interfaceは具体的に：(1) current Domain value/binding→fresh scope-bound ordinary read ref、(2) scope/loan historyとref currentness、(3) active loan→Domain consume/transfer/finalize guard、(4) body exactly-once / result＋surviving-state dependency保存とscope exit。これらを新しくstipulateして成功させていない。

## 非空frameと攻撃

witnessはretired D=0 / retired source value7のghost historyから、**D_B=1 / original D value1009**を発行。rich domain mapはD1→carrier1009、old D0はliveでない。D0 historyはPRE入力であり、R_C=0やaddress/Copy ptrから推論していない。新DとR_Bの数値が異なることに意味を依存させない。

A_B=1004、slot_B=1008、old C graph、rich active claims **{10,0}**、full bytes、physical state、incarnation historyはそのまま。Dを発行してもtyped Node開始やcurrent ptrを与えない。

| 攻撃 | 証明・境界 |
|---|---|
| 同じDを第二nonCopy valueへ複製 | source domainUniqueが拒否。rich byte WFは変わらない |
| 同じD/valueをlocalとresult双方へ複製 | distinctPlacesが拒否。unionだけの検査では不十分 |
| 一個のvalueから異なるD identityをclone | source valueUniqueが拒否（このsingle-value profile） |
| retired D0 / old R_C番号からD0を再発行 | computed source fresh名とhistoryが拒否。F0だけではretired reuseのWF stateが作れるがRefinesDomainは拒否 |
| 同一selected eventの二重発行 | single-call phase/current-domain条件が拒否。別のfresh Dを作る一般的な二回目callをlanguage-invalidとはしない |
| 同じD/valueの二重consume | first forwardでlocalをeraseし、secondのavailable前提が不成立 |
| Dのnormal-result紛失 | NormalExit inventory completenessが拒否 |
| original Aまたはempty slot紛失 | source owner invariantが拒否 |
| current typed root/ptr/incarnationを捏造 | source extras、rich occupancy refinementが拒否 |
| Copy ptrから次のD番号をguess | actual event前のcurrent inventoryにDはない。発行後もptr値だけではaccepted object refを取得できない |
| source PREにrich Dをfabricate | current-domain/carrier refinementが拒否 |
| unvalidated loan下でrich transfer/finalizeを許可 | allowed=True projection controlsは成立。scope guardの未証明を示す。canonical loan safetyの反例ではない |
| ref escape | registered scope dependencyはreject、DomainLiveのみではprotectしない。実際のDomain-value refへの登録bridgeはHOLD |
| old issuer Noneを繰り返す |全source/geometry/rich/interpretation identity。Noneにslot/Domain successorはない。lifetime_domain自体へ架空のNone armは追加しない |

## trusted境界・historical audit・検証・停止

trusted：canonical atomic Domain issuerのfresh opaque責任契約、source history/nameのα-renaming解釈、F55のtrusted builtin/layout/supply/Node typing。proved：その契約の明示source inventory、computed current grant、F0 Domain live/carrier構成、rich WF/Accountingとowner/byte frame。未証明：actual AST/parser/checker/native Domain factory、generic/FFI/ABI、lexical Domain ref/scope applicability、native correctness。

Historical A–C：固定Draft17.30 §§3.2/13をnormative-currentとしてKEEP。DI009のdistinct A/Storage/slot/Dとexplicit lifecycle、DI010のscoped stability/mode preservation、DI011–014のconditional known-call / LiveTail / durable custody / five-root boundariesをKEEP。このtaskではそれらのtyped ownerやcallを使わずDEFER。旧Surface Draft1/1_1はnon-normative、current lawへ昇格しない。Process §4.2とDesign Decision Procedureを確認し、**N/A — faithful proof of selected §13 source law; formal representation research only**。final loan syntax/APIの選択、canonical/ledger修正、DI015 adoptionを行わない。旧M9全文は独立に網羅確認していない。

新規四module **84 explicit declarations / 47 theorems**（source25/10、rich13/10、witness12/6、controls34/21）を全て既存auditへ追記。audit logic/allowlistと受理済みF0/F1/adjunctは無変更。ローカル最終`lake build`は814 jobsで成功、`scripts/check-proofs.sh`は2108 theorem axiom reportsを検証して成功。初回の公開はconnectorの`Unknown tool`で停止したが、GitHub plugin接続復旧後に同じproof-only候補の公開を再開した。CLIのsocket作成拒否は残るためconnectorを使用する。candidate head・DRAFT PR・exact-head GitHub Actionsの最終結果はPRとIssue #57の一回の報告に記録する。audit総数は2024+84=2108。standard Lean logicのみ、custom axiom/placeholderゼロ。

2026-10-11 08:10 JSTから開始した2–4h上限のtask。fresh issuer後の最初のloan interfaceでHOLDとし、以後は同じscopeのnegative controlsとaudit/publicationのみ。initialize、typed H開始、ptr取得、destroy/deallocate、5-root、detach/adopt、terminal cleanup、0..5 allocation、6+4+2、general allocator/native、S1/H1は実施しない。DRAFT PRのmerge、Issue closeは行わず、自己merge・自己close・他Track起動をせず停止する。

F SLOT→FRESH DOMAIN ISSUER: HOLD — EXACT DOMAIN/RICH BRIDGE UNPROVED
