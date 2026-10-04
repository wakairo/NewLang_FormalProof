# NewLang F0 Formal Kernel — F0.0

NewLang v0 semantic kernelのLean 4形式化の最小基盤です。今回の対象はidentity、Fact、ValuePackage、flat State、LiveFacts、WellFormedのみです。operationとtransition preservationはまだ実装していません。

## 仕様の優先順位

1. [NewLang v0 Draft 17.4](docs/NewLang_v0_spec_Draft17_4.md): normative specification / source of truth。
2. [F0 Formal Kernel Specification Draft 0](docs/F0_Formal_Kernel_Specification.md): non-normative bridge。添付資料を変更せず保存しています。
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

LiveFactsは現在のoccupancyにあるfactだけを含み、履歴のfactを別途liveにしません。mapsのfinite supportと歴史全体に対するfreshnessは今回のstate invariant theoremでは証明しません。transitionを追加する際に必要なhistory/freshness premiseを明示し、現在使われていないIDであればfreshだと短絡しないでください。

## Kernelによるsmoke確認

`wellFormed_surviving_dependencies_live`は、WellFormedからsurviving packageの各dependencyがliveであることを導きます。`empty_wellFormed`は空状態が実際にinvariantを満たすことを証明します。

`lake build`で全プロジェクトsourceとproofをチェックします。`scripts/check-proofs.sh`はprojectの`.lean` sourceをscanし、proof placeholder / added axiomがないことと、2つのtheoremの`#print axioms`結果を確認します。両theoremが依存するのはLean標準logicの`propext`、`Classical.choice`、`Quot.sound`のみです。semantic invariantを公理として追加していません。

docsにある概念コードやaxiom policyの説明、mathlib自身はproject sourceのscan対象ではありません。

## 次のF0.1

次はF0 bridge §28に沿って`replace`のrelational RawStep/Step、fresh current fact、old packageのloose resultへのtransferを追加できます。old packageがold current factへ依存すると合法なreplaceが存在しないnegative lemmaも対象です。今回、これらのtransitionやpreservation theoremは先行実装していません。NewLang全体のtype safety/compiler correctnessも主張しません。

資料上の注意とencoding境界は[formalization notes](docs/FORMALIZATION_NOTES.ja.md)を参照してください。
