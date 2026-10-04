# NewLang F0 Formal Kernel — F0.1

F0.0のflat State / WellFormed基盤に、F0.1としてproof-only historical freshnessと`replace`を追加しました。preservationとdependency non-launderingをmachine-checkしています。今回実装したoperationは`replace`のみです。

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

Raw replaceは新IDをinsertし、以前の履歴全体を保持します。`replace_history_monotone`と`replace_old_fact_remains_used`を証明しました。現在deadでも使用済みのIDはfreshではありません。countermodelではID 2がその具体例です。初期状態には過去の割当てをすべて記録し、将来のallocating transitionも履歴を保持・拡張する必要があります。live factsだけから履歴を再構成してはいけません。

この履歴は**proof-only ghost state**であり、NewLang compiler/runtimeにhistory setを要求しません。F0.4では同じ方式で`usedIncarnations : Finset IncarnationId`へ自然に拡張できますが、今回は未実装です。finite-support、payload、authority algebra、borrow checker、structural places、scope/backing facts、他operationも未検証です。

## replace semantics

`replaceCandidate`はtarget locationのcurrent factとpackageだけを更新し、PlaceId・IncarnationId・governing DomainId・root location・live-root statusを保持します。他location、package data、live domainsも変えません。incomingをloose集合から除去し、old packageをloose resultとして追加し、used historyへ新factを追加します。

`RawReplace canWrite typeCompatible s location root incoming newFact s'`はpre-stateのlive root、incoming loose、historical freshness、callerが証明するwrite/type compatibility premise、candidateとの等式を保持します。resultは`root.package`です。production側ではauthorization premiseを常にTrueと定義しません。countermodelのみTrueを与えてstate/dependency ruleを独立に検証します。exclusive refやlifetime-ending authorityは要求しません。

`ReplaceStep`は`WellFormed s ∧ RawReplace ... ∧ WellFormed s'`です。preservation theorem自体はpost-state条件のprojectionですが、raw transitionがすべて合法になるという主張ではありません。candidateの具体的更新、carrier transfer、freshness、old factのinvalidation、surviving dependencyからのrejectを別々に証明しています。依存のないlegal replaceの具体例も証明済みです。

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

`lake build`はproductionとcounterexampleの両moduleをチェックします。`scripts/check-proofs.sh`はproject-owned Lean sourceの`sorry` / `axiom` / `admit`をscanし、23 theoremのaxiom reportを検査します。許可するのはLean標準の`propext`・`Classical.choice`・`Quot.sound`のみです。Leanの失敗statusを保持し、複数行のreportにも対応します。docsのproseとmathlib sourceはproject-source scanの対象外です。

## GitHub Actions

[`.github/workflows/lean.yml`](.github/workflows/lean.yml)はpush / pull_requestで実行します。read-only repository permission、Ubuntu 24.04、commit-pinned checkout v6.1.0を使用し、bootstrap prerequisitesを導入します。空のrunner temporary toolchain/cache pathで`bash scripts/bootstrap.sh`を実行し、固定toolchain / manifestによる`lake build`とproof checkerを実行します。latest Leanへのupgradeやmanifest更新は行いません。追加secretやserviceは不要です。

## Canonical milestone sequenceと次のF0.2

| Milestone | Scope |
| --- | --- |
| F0.0 | State / WellFormed — 完了 |
| F0.1 | replace — 完了 |
| F0.2 | store — 次 |
| F0.3 | swap |
| F0.4 | initialize / take / destroy |
| F0.5 | ptr / ref acquisition |
| F0.6 | LifetimeDomain transfer / finalization |

次は`store`です。historyとcandidate/dependency machineryを再利用できますが、old packageはresultとしてsurviveさせずconsumeする必要があります。store以降のoperationは今回は実装していません。NewLang全体のtype safetyやcompiler correctnessも主張しません。

[formalization notes](docs/FORMALIZATION_NOTES.ja.md)と[F0.1 report](docs/F0_1_REPLACE_REPORT.md)も参照してください。
