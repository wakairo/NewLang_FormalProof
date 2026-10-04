# NewLang F0 Formal Kernel — F0.4

F0.3までのstate / replace / store / swap基盤へ、F0.4のinitialize / take / destroyとhistorical incarnation freshnessを追加しました。同じ自己依存pre-stateでtakeは拒否・atomic destroyは合法です。initialize → take → 同じsiteでinitializeの経路で、旧IDを履歴に残したまま異なるincarnation/current factを使うことをmachine-checkしました。ptr/ref acquisitionはF0.5です。

## 仕様の優先順位

1. [NewLang v0 Draft 17.4](docs/NewLang_v0_spec_Draft17_4.md): normative specification / source of truth。
2. [F0 Formal Kernel Specification Draft 0](docs/F0_Formal_Kernel_Specification.md): non-normative bridge。milestone番号のみを修正し、FORMAL-EXTRACTIONの解決履歴として記録しています。Draft 17.4は変更していません。
3. Lean model: proofのためのencoding。

**Formal representation choices are non-normative.**

Natで包んだID、Finset、関数によるmap、Boolのdiscardability、PackageIdは、NewLang compiler/runtime representationの要求ではありません。証明しやすさを理由にnormative semanticsを変更しません。

## 固定した環境

| Component | Pin |
| --- | --- |
| Lean / Lake | `leanprover/lean4:v4.34.1` (`lean-toolchain`) |
| Lean release commit | `5045d0056413266e57c625dcd7c365b10e377c52` |
| elan | `4.2.4` (cloud bootstrap) |
| mathlib | `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Transitive dependencies | `lake-manifest.json`のfull Git SHA |

2026-10-04のセットアップ時点でLeanとmathlib双方の最新stable releaseはv4.34.1でした。mathlib自身の`lean-toolchain`も同じバージョンなので、このcompatible pairを採用しました。mathlibは`lakefile.toml`とmanifestの両方でcommitに固定しています。

## Codex Cloudでの再現

既存checkout `/workspace/NewLang_FormalProof` を使用します。各cloud taskは既に隔離されているため、追加worktreeは作りません。このcheckout自体が概念上の`newlang-formal/` rootです。

必要なbase tools: Bash、Git、curl、tar、zstd、sha256sum、ripgrep。Lean/mathlibがpreinstalledであることには依存しません。

```bash
cd /workspace/NewLang_FormalProof
bash scripts/bootstrap.sh
export ELAN_HOME=/workspace/.local/elan
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR=/workspace/.cache/mathlib
lean --version
lake build
bash scripts/check-proofs.sh
```

bootstrapは公式GitHub releaseのelanとLean archiveを固定SHA-256で検証してから展開し、`elan toolchain link`でrepositoryのtoolchain名へ登録します。TLS検証を無効にしません。Leanのrelease-discovery endpointに依存せず再現できる経路です。checksumは公式GitHub releaseのasset digestから取得しました。

依存解決には既存manifestを使い、`lake update`は実行しません。今回importするmathlibの591-module closureのcacheだけを取得し、プロジェクトをbuildします。cacheが取得できない場合も、同じsourceを`lake build`でcompileできますが時間がかかります。新しいimportを追加したら、そのmoduleに対して`lake exe cache get Module.Name`を実行できます。mathlib全体のrebuildは通常不要です。

設定を将来変更するときはtoolchain、mathlib revision、bootstrap checksum、manifestをまとめて更新・検証してください。通常のセットアップでlockfileを更新しないでください。

ネットワークはGitHub/Git proxy、`release-assets.githubusercontent.com`、`cache.mathlib.org`、`lakecache.blob.core.windows.net`を使用します。通常の`elan toolchain install`にはelan 4.2.4の`release.lean-lang.org`も必要です。既存のpackage-manager presetを保持し、これらを必要に応じて環境設定で許可してください。アプリ用secretやserviceは不要です。

新しいCodex Cloud taskへ準備済み環境を保持するには、保存した環境設定をreview/saveしてPublishしてください。Git checkoutから再現する場合は、repository内のbootstrapと固定manifestを使用してください。

## その他の開発環境

通常のelanインストールが利用可能なら、repository rootで次を実行します。

```bash
elan toolchain install leanprover/lean4:v4.34.1
lake exe cache get Mathlib.Data.Finset.Basic Mathlib.Data.Set.Basic
lake build
bash scripts/check-proofs.sh
```

x86_64 Linuxではcloud bootstrapも利用できます。cloud以外では書込み可能な場所を指定してください。

```bash
ELAN_HOME="$HOME/.elan" \
NEWLANG_TOOLCHAIN_ROOT="$HOME/.local/share/newlang-lean" \
MATHLIB_CACHE_DIR="$HOME/.cache/mathlib" \
bash scripts/bootstrap.sh
```

通常のelanインストール手順は他OS向けの代替で、このtaskではcloud用bootstrapを検証しています。

## Modelとtraceability

| File / definition | Scope / source |
| --- | --- |
| `Id.lean` | nominally distinctな6種類のID (F0 §4) |
| `Fact.lean` | `valueFact(PlaceId, ValueFactId)` / `domainLive(DomainId)` (F0 §5) |
| `Package.lean` | 有限dependency集合とdiscardability。payload/authorityは省略 (F0 §6) |
| `State.lean` | vacant/live occupancy、package table、loose packages、live domains (F0 §7–9) |
| `LiveFacts` | occupancyとlive domainsから導出するview (F0 §5; Draft 17.4 §13.5a) |
| `CarrierUnique` | installed/looseの同時存在と二重installationを排除 (F0 WF-1) |
| `PlacesUnique` | 一つのplaceには一つのlive root/current fact (F0 WF-4; Draft 17.4 §13.5a) |
| `IncarnationsUnique` | 一つのincarnationは一つのlive rootを識別 (Draft 17.4 §3.5) |
| `PackagesPresent` | installed/loose carrierは存在するpackageのみを参照 (F0 WF-7) |
| `DomainsValid` | governing domainのliveness (F0 WF-5; Draft 17.4 §13.2) |
| `DependenciesValid` | surviving packageのdependencyがLiveFactsに含まれる (F0 WF-6; Draft 17.4 §13.5a) |

WF-2/3/8はdatatypeとderived carrierにより構造的に表現します。carrierはlocationで区別し、`PlacesUnique`によりWellFormedなstateでplaceと対応させます。同じplaceを持つ異なるrootが不正に二重installationされてもcarrier uniqueness checkから漏れません。

`occupancy`はtotal function、`packages`はOptionを返すpartial mapです。package tableにcarrierを持たない記録が残ってもsurvivorではありません。loose carrierだけの場合もmissing packageを許しません。すべてのsurviving packageを状態に明示するF0 abstractionであり、source syntaxのbindingを直接モデル化していません。

## Historical freshness: proof-only ghost state

`State.usedValueFacts : Finset ValueFactId`にexecution historyで割り当てたIDを記録します。`FreshValueFact s vf`は`vf ∉ s.usedValueFacts`です。`WellFormed.valueFactsRecorded`により、liveなcurrent factは必ず履歴へ含まれます。`State.empty`の履歴は空で、既存smoke theoremは再証明済みです。

Raw replaceとRaw storeは新IDをinsertし、distinct swapは互いに異なる2つのfresh IDをinsertします。same-place swapでは割当てを行いません。すべて以前の履歴全体を保持します。storeも同じ`FreshValueFact` / `ValueFactsRecorded`を再利用し、history monotonicityとold factの履歴保持を証明しました。現在deadでも使用済みのIDはfreshではありません。countermodelではID 2がその具体例です。初期状態には過去の割当てをすべて記録し、将来のallocating transitionも履歴を保持・拡張する必要があります。live factsだけから履歴を再構成してはいけません。

この履歴は**proof-only ghost state**であり、NewLang compiler/runtimeにhistory setを要求しません。F0.4で同じ方式の`usedIncarnations : Finset IncarnationId`、`FreshIncarnation`、`IncarnationsRecorded`を実装しました。既存candidateはincarnation historyを完全保存し、fixtureではlive incarnationをseedします。initializeだけが両historyを拡張し、take/destroyはended IDも消しません。これはproof encoding extensionであり、F0.1–F0.3のsemantic revisionではありません。finite-support、payload、authority algebra、borrow checker、structural places、scope/backing facts、他operationも未検証です。

## replace semantics

`replaceCandidate`はtarget locationのcurrent factとpackageだけを更新し、PlaceId・IncarnationId・governing DomainId・root location・live-root statusを保持します。他location、package data、live domainsも変えません。incomingをloose集合から除去し、old packageをloose resultとして追加し、used historyへ新factを追加します。

`RawReplace canWrite typeCompatible s location root incoming newFact s'`はpre-stateのlive root、incoming loose、historical freshness、callerが証明するwrite/type compatibility premise、candidateとの等式を保持します。resultは`root.package`です。production側ではauthorization premiseを常にTrueと定義しません。countermodelのみTrueを与えてstate/dependency ruleを独立に検証します。exclusive refやlifetime-ending authorityは要求しません。

`ReplaceStep`は`WellFormed s ∧ RawReplace ... ∧ WellFormed s'`です。preservation theorem自体はpost-state条件のprojectionですが、raw transitionがすべて合法になるという主張ではありません。candidateの具体的更新、carrier transfer、freshness、old factのinvalidation、surviving dependencyからのrejectを別々に証明しています。依存のないlegal replaceの具体例も証明済みです。

## store semantics

visible value levelでは、storeはreplacementの旧値をdiscardする動作に相当します。ただしdependency legalityでは**一つのcombined transition**です。「legal ReplaceStepを先に要求し、そのresultをdiscardする」という定義ではありません。

`storeCandidate`はtargetのcurrent fact / packageを更新し、incomingとoldのloose carrierを除去します。package tableとlive domainsを保存し、新factをhistoryへ追加します。`RawStore`はwrite/typeのcaller premiseと、旧`ValuePackage`の存在・`discardable = true`を要求します。incomingのdiscardability、exclusive ref、lifetime-ending authorityは要求せず、destructor / Drop semanticsも追加しません。

`StoreStep = WellFormed pre ∧ RawStore ∧ WellFormed post`です。unit resultには旧値のcarrierがありません。pre-stateのcarrier uniquenessがincoming = oldと旧値の二重installationを排除するため、旧packageはpost-stateでsurviveしません。table recordは残しますが、carrierのない記録は`DependenciesValid`の対象外です。これはproof encodingであり、runtimeの物理削除やmemory managementの要求ではありません。

preservation自体はpost-state条件のprojectionです。実質的な性質としてcarrier消費、old factの失効、frame、history保持を別に証明しました。同じ初期状態のself-dependentなdiscardable旧値について、replaceは拒否されstoreは合法です。第三のloose survivorやincomingが同じdependencyを持つ場合はstoreも拒否します。discardability guardを省くとpost-stateがWellFormedでもnon-discardable旧値を失えるため、このguardはtransition legalityに必要です。

## swap semantics

`SwapCase.same location root`にはfresh ID引数がありません。`RawSwapSame`はlive targetとcallerの両write/type premiseを要求し、`post = pre`です。current fact・package・incarnation・domain・loose carrier・historyを含む全fieldが不変で、self-dependencyもlegalです。

`SwapCase.distinct` / `RawSwapDistinct`は異なるlive locations、両write authorization、type agreement、2つのfresh factsを要求します。`FreshValueFactPair s a b`は両方がpre-historyに未使用かつ`a ≠ b`です。WellFormedのplace uniquenessがplaceの相違を保証し、carrier uniquenessからinstalled packageの相違を導くため、後者をraw premiseへ追加しません。

`swapCandidate`は一つのatomic exchangeです。place・location・incarnation・governing domainをそれぞれ保持し、package IDsを交換、current factsをfreshenします。他location、package/dependency data、loosePackages、liveDomainsは不変です。旧historyをすべて保持して新ID双方を記録し、replace/take/initializeの中間stateを作りません。dependency retargetingやdiscardも行いません。

`RawSwap`はこの2つのcaseだけをdispatchし、`SwapStep`はWellFormed pre/raw/postを検査します。`SwapSameStep` / `SwapDistinctStep`はcase別のabbreviationです。caller premiseはabstract Propのままで、fixtureだけにTrueを与えます。**F0.3 does not introduce a Copy requirement.** Discardable・exclusive ref・lifetime-ending authorityも要求しません。両packageがnon-discardableで、governing domainsが異なるlegal witnessを証明しました。

両旧packageは相手locationでsurviveし、両旧factはdeadになります。通常のpost-state `DependenciesValid`だけでself/cross/cyclic/第三survivorの依存を拒否します。同じ自己依存pre-stateでsame-placeは合法、distinct-placeは拒否です。cyclic raw candidateは他のWellFormed fieldをすべて満たし、dependency validityだけに失敗します。

## Lifetime / occupancy semantics

F0.4ではsource-level slot/ptr/refとbacking geometryを、root location・Vacant/live occupancy・package carrier・domainで抽象化します。**Root-only requirement is structurally satisfied by F0 scope.** すべてのlive occupancyがlifetime rootで、Vacantは同じsiteのempty occupancy responsibilityです。slot value、PtrToken、subobject、Storage、BackingRegionは導入しません。

`RootSiteLayout`は実行のproof contextで固定するinjectiveな`RootLocationId → PlaceId`対応です。initializeは同じlayout/siteからPlaceIdを得るため、fresh PlaceIdをmintしません。nominal型を分離したまま、既存stateへglobalなlayout-coherence invariantを追加しません。既存operationはplaceを保持します。lifecycle witnessでは同じlayout/locationでplaceが同一、incarnationが異なることを証明します。fixtureの数値対応はruntime formatを意味せず、FORMAL-ENCODINGとして扱います。

`RawInitialize`はvacant target、loose incoming、渡されたlive domain、fresh incarnation/current fact、ordinary initialization authorizationとtype agreementを要求します。incomingをinstallし、**渡されたdomain**へのgoverning relationを作り、両IDをhistoryへ記録します。Discardableやlifetime-ending authorityは不要です。package tableを変更せず、incomingのdata/dependencyからgoverning relationを復元しません。

`RawTake` / `RawDestroy`はlive root、`endingDomain = root.governing`、callerが証明するabstract Prop `CanEndRoot`を要求します。productionで常にTrueとしません。両方ともincarnation/current fact/governing relationを終了してVacantへ戻し、**DomainId自体はliveのまま**です。他location、package data、両historyは保存します。takeは旧値をloose resultへ返し、non-discardableも許します。destroyは旧値のdiscardabilityを追加要求してcarrierを消費し、inactiveなtable recordは残して構いません。

visible value levelではdestroyはtake後のdiscardに相当しますが、dependency legalityは一つのcombined candidateで判定し、legal TakeStepを先に要求しません。old-only self-dependencyはtakeを拒否しdestroyでは消費できます。他survivorが同じ依存を持つ場合は両方rejectします。**destroy uses the existing proof-side abstraction; this is not a runtime package flag requirement.** destructor/Dropは追加しません。

3つのStepはWellFormed pre/raw/postを検査します。preservationのprojectionに加え、carrier/history/frame、identity終了、dependency拒否を個別証明しました。initialize/take/reinitializeの具体例は同じvacancyとunique loose carrierを復元しますが、履歴は元へ戻さず旧incarnationの再利用を拒否します。Governs / LiveIncarnationはderived viewで、別のmutable relation tableではありません。

## Machine-checked theorem一覧

以下は`NewLang.F0` namespaceです。

| Theorem | 性質 |
| --- | --- |
| `wellFormed_surviving_dependencies_live`, `empty_wellFormed` | 既存F0.0 smoke proof |
| `replace_preserves_wellFormed` | Legal replaceのinvariant保存 |
| `replace_preserves_incarnation`, `replace_preserves_governingDomain` | Lifetime stateの保存 |
| `replace_preserves_place_and_location`, `replace_preserves_other_locations` | Target identity/statusとframe |
| `replace_preserves_package_data_and_domains` | Dependency dataとdomain集合の保存 |
| `replace_creates_fresh_current_fact` | Pre-historyに未使用、post-current、post-historyに記録 |
| `replace_history_monotone`, `replace_old_fact_remains_used` | 使用履歴の保持 |
| `replace_old_package_survives_as_loose` | Old packageがresultとしてsurvive |
| `replace_new_package_installed` | Incomingがinstalledになりlooseから消える |
| `rawReplace_old_current_fact_not_live` | Raw replace後にold current factがdead |
| `replace_rejects_surviving_old_current_dependency` | Old package側のnon-laundering |
| `replace_rejects_incoming_old_current_dependency` | Incoming側のold-current dependencyもreject |
| `replace_rejects_previously_used_fact` | Retired IDを含めhistorical reuseをreject |

`NewLang.F0.Counterexample.Replace`には`before_wellFormed`、`independent_replace_is_legal`、`unchecked_replace_launders_old_dependency`、`old_dependency_is_rejected`、`incoming_dependency_is_rejected`、`currently_dead_is_not_historically_fresh`があります。dependency checkを外したraw candidateは他のWellFormed fieldをすべて満たし、`DependenciesValid`だけが失敗します。broken Stepをproduction namespaceへ追加していません。

F0.2ではstoreのWellFormed / incarnation / governing domain / place / location / frame保存、fresh factと履歴保持、incoming installation、旧package非survival、old fact失効、other survivor保存、第三survivor・incomingのdependency拒否、non-discardable拒否、使用済みfact再利用拒否を証明しました。具体的なreplace/store対比と3種類のbreak-testを含む全定理一覧は[F0.2 report](docs/F0_2_STORE_REPORT.md)を参照してください。既存F0.1 proofもすべて維持しています。

F0.3の45定理（production/helper/fixture）の一覧と、same-caseのidentity・distinct-caseの保存/交換/2-fact freshness・old fact失効・self/cross/cyclic/第三survivor拒否・non-discardable witness・履歴再利用/新ID衝突拒否・broken dependency checkは[F0.3 report](docs/F0_3_SWAP_REPORT.md)を参照してください。既存F0.0/F0.1/F0.2 proofも維持しています。

F0.4で78定理を追加auditします（既存operationのincarnation history保存4、lifetime production/helper 54、具体的fixture 20）。初期化・occupancy conservation・fresh reinitialize・take/destroy対比・domain lifecycle・authorization/discardability拒否・3種類の破壊試験の全一覧は[F0.4 report](docs/F0_4_LIFETIME_OCCUPANCY_REPORT.md)を参照してください。既存theorem statementとsemantic claimは変更せず、ghost historyをseedして従来の102 auditもすべて通っています。

`lake build`はproductionとcounterexampleの両moduleをチェックします。`scripts/check-proofs.sh`はproject-owned Lean sourceの`sorry` / `axiom` / `admit`をscanし、180 theoremのaxiom reportを検査します。許可するのはLean標準の`propext`・`Classical.choice`・`Quot.sound`のみです。Leanの失敗statusを保持し、複数行のreportにも対応します。docsのproseとmathlib sourceはproject-source scanの対象外です。

## GitHub Actions

[`.github/workflows/lean.yml`](.github/workflows/lean.yml)はpush / pull_requestで実行します。read-only repository permission、Ubuntu 24.04、commit-pinned checkout v6.1.0を使用し、bootstrap prerequisitesを導入します。空のrunner temporary toolchain/cache pathで`bash scripts/bootstrap.sh`を実行し、固定toolchain / manifestによる`lake build`とproof checkerを実行します。latest Leanへのupgradeやmanifest更新は行いません。追加secretやserviceは不要です。開発は専用branchからmain向けPRを作成し、pull_request-triggered Lean proofsの成功を確認します。PRはsemantic reviewまでopenのまま残し、CI成功だけでmergeしません。

## Canonical milestone sequenceと次のF0.5

| Milestone | Scope |
| --- | --- |
| F0.0 | State / WellFormed — 完了 |
| F0.1 | replace — 完了 |
| F0.2 | store — 完了 |
| F0.3 | swap — 完了 |
| F0.4 | initialize / take / destroy — 実装済み、PR review待ち |
| F0.5 | ptr / ref acquisition — F0.4 review後の次milestone |
| F0.6 | LifetimeDomain transfer / finalization |

F0.4のreview・merge後はhistorical incarnation、LiveIncarnation、same-site fresh reinitialization proofを使ってF0.5へ進めます。PtrToken/ref acquisition、domain finalization、backing geometry、structural subobjectsは未実装で、NewLang全体のtype safetyやcompiler correctnessも主張しません。

[formalization notes](docs/FORMALIZATION_NOTES.ja.md)と[F0.1 report](docs/F0_1_REPLACE_REPORT.md)、[F0.2 report](docs/F0_2_STORE_REPORT.md)、[F0.3 report](docs/F0_3_SWAP_REPORT.md)、[F0.4 report](docs/F0_4_LIFETIME_OCCUPANCY_REPORT.md)も参照してください。
