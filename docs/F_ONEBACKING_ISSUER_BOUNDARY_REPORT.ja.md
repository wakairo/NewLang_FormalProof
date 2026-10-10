# F #51 — original OneBacking issuerとaccepted-rich初期状態の最初の境界

Track: F

**HOLD — A（元Allocation/full Storage発行）のsource→accepted-rich interfaceは未実装である。** 実Cの成功経路でsame fresh region/full raw/一つのAllocation/current nested carrierを観測・検査した。一方、accepted Backing/OccupancyにはAllocation値の発行・origin解釈がなく、raw claimもinitializeも既にliveなRを要求する。発行後のWorld/full claimを入力として与えるだけではAの証明にならない。最初のこのinterfaceで停止し、B/C、二member after-A terminalへ拡張しない。

## 固定authorityと手順

- FormalProof/main base: `f7dcac614394a526ea9c33848cafd324f2993d19`。新branch `f51-onebacking-issuer`。F49/PR50はCoordinationによりACCEPT-AS-HOLD、補助証明のみmerge済み。
- Compiler/main: `b75baea96a644e68634baee383299b66981b3c62` / canonical `CURRENT_SPEC.md` **Draft17.30**。
- 凍結P280: `4bc6b690e87b4646596dfd460bea26e9a5d8dac5`。実source/issuer/checkerをread-only checkoutで確認。PのsnapshotをLean仮説にしない。
- M273: `f778eba116d1834cc79c0bef6f6c17051102049f` / proposed Draft17.31/DI015はUNADOPTED。P284はparser HOLDであり、genuine owner proofではない。将来のP成功には依存しない。
- Issue51、F43/F47/F49 reports、Issue49のCoord裁定 `6096621925`、P278の凍結source evidenceとaccepted F0/F1 constructorsを確認。Process §2/4.2/6/7、canonical §§3.1–3.4、4、13–18、26–27の関連issuer/lifetime/ordinary nonCopy規則を照合。
- **Historical design audit: N/A — faithful proof study of selected core。** 既存constructorの境界・観測・反例のみ。新しいAllocation authority assumption/semantic constructorは導入していない。新しいsemantic authority extensionが必要ならUNSELECTED candidateとしてCoordinationのGate A–Eへ戻す。今回それを選択・実装しない。

## 実際の発行・消費経路

### A: issuer

`src/allocated_node.c:nl_allocated_registry` は実登録されたNodeのcompleted typeを使い、private target layoutを登録するだけで、R/A/D/rootを発行しない。one-link Nodeは24 byte、P278のthree-link Nodeは56 byte、alignment 8というこのtargetのrepresentation planでありsource ABI契約ではない。

`nl_allocated_grant(success=true)` → `src/raw_storage.c:nl_raw_apply(NL_RAW_ALLOCATE)` は:

1. size/alignment/platform-profileを検査し、region entryを**append**する。Rのordinalは新しい`region_count`。同一contextの過去entryを再利用しない。
2. raw interval `[0,size)` を一つ作り、ordinary read/write factsをregion viewへ設定する。
3. 新しいAllocation valueの`allocation_region`と新しいStorage valueの`occupancy.region`を、同じ新regionにする。Storageのstart=0、length=size。
4. 実際の二value IDsをOneBackingの`fields[0/1]`へmove-inし、両memberを`NL_CARRIER_AGGREGATE`/owner=bundleへ変更する。
5. bundleをSomeのpayloadへmove-inし、bundleを`NL_CARRIER_SUM`/owner=sumへ変更する。None経路ではR/A/rawを作らない。

これはstatic checkerのowned state操作である。interval配列のhost mallocをNodeのnative backing primitiveの証明と同一視しない。`region_count`はsource World/clone lineageに相対的であり、別contextの同じ整数やmachine addressから同じ元Rを推論しない。成功後のWorld解釈には既存identityのframeと新しいabstract bytes/non-aliasの対応が必要。

`nl_raw_validate` はEnded以外の実Allocation valuesを、aggregate/sum memberも含めて数える。各live regionのAllocation数が**ちょうど1**、byte責任の総量がsize、範囲が正・inbounds・非重複、raw intervalsが全rangeを覆うことを検査する。`nl_sem_validate`（fixed/sum validators）がmember→owner/current carrierの整合を別に検査する。issuer/byte accountingだけではこのCのcarrier検査も代用できない。

canonical mainと凍結P280間の`src/allocated_node.c`、`src/raw_storage.c`は**全fileで差分なし**。SHA256:

- allocated_node.c: `a18b756e68ec8d06d2e191c6751a49c81c265892fe07c16f6311cdadaa4b331e`
- raw_storage.c: `470b01ffdcebe89b0c5b6d8bb4a3a7e879af19c47fb99ffd879965aabbc03c9f`

### B: typed root

source whole match/destructureはSome/OneBackingをconsumeし、実memberをLOOSEへ取り出す。`NL_RAW_INTO_SLOT` はcurrent rawを要求し、exact target size/alignmentを再検査してその同じrangeをslotへ移す。`lifetime_domain()` → `nl_sem_new_domain` はdomain entryをappendし、新しい非Copy valueをそのdomainのcurrent valueとして登録する。

`semantic_check.c:primitive(NL_CHECKED_INITIALIZE)` はreal slot/value/domain-refを検査し、`nl_sem_install`/`nl_raw_start_root`で同じrangeのrootを作り、そのheap place/current incarnation/governing domain/accessを持つptrを返す。これらの実C factsを、accepted `RawInitialize`が自動的にsourceから生成された証拠としては使わない。

### C: ordinary carrier

実CのSome/OneBackingには通常のnested非Copy carrierが存在する。純粋なrecord/returnがmatched release permissionを新設するわけではない。F49のmixed-ordinary-return/repaired positiveとwrong-A-at-use negativeはretained evidenceであり、今回はnamed assembler/whole returnのsimulationを作らない。元A/Dのsemantic interpretationを先に与えてから「普通に移動すれば保存」と言っても、Aのproductionを証明したことにはならない。

## 独立実行: source観測・直接issuer・owned poisonを区別

`experiments/run_f51_onebacking_probe.py` / `f51_onebacking_probe.c` は凍結checkoutを読み、未変更のCMake source listsの非LLVM library sourcesをGCC14.2/C17/-O0/-g/-Wall/-Wextra/-Wpedantic/-Werrorでbuildする。P278 sourceのparser/registrationには三default-OFF experimental flagsを明示する。Compiler filesは編集しない。CMake全profile/LLVM/native/OOM sweepの実行は主張しない。

**13個の観測・control assertionsが成功、probeを二回実行してJSONが完全一致。** 再実行可能な結果は`docs/experiments/F51_ONEBACKING_OBSERVATIONS.json`に収録。

| 実験区分 | 入力と結果 | 証明上の限界 |
| --- | --- | --- |
| actual source→owned artifact | canonical `allocated_node_semantic.nl`をparse/register/main()実check。元A/rawのsame R/full24、actual initialize/destroyの同O/inc/D、元A/raw Ended・R dead・一free、owned validators PASS | sourceのone-root有限観測。Lean evaluatorではない |
| immediate production issuer | 上記Nodeと**実P278 sourceを登録したNode**の両方へ、production `nl_allocated_grant`を直接呼ぶ。登録直後R/D/value=0、Noneはgrantなし、Someはfull24/full56、一R、typed root/D未作成、実Some/OneBacking/member IDsとowner treeを検査 | private primitive direct-call experiment。P278 mainの全source実行や全carrier移転ではない |
| malformed owned-state poison | duplicate A、AだけEnded、最後の1 byte不足、Aのaggregate ownerを別kindのsumへ変更 | sourceから構築できるstateとは主張しない。前3件はraw validator拒否。wrong carrierは**raw validator PASSでもsemantic validator拒否** |
| actual raw requiring use | genuine別RのA_C + R_BのrawでP4-ALLOCATION-MISMATCH。8 byteを7+1へsplitしprefix単独のdeallocateはP4-FULL-RANGE-REQUIRED。merge後は合法終了 | 実C raw primitiveの拒否。accepted-rich Allocation release judgmentの証明ではない |
| address reuse | 既存raw primitive profileで4096を使い、元R終了後同addressで新Rを発行。R ordinalは異なる | numerical address一致はidentity証明でない。native allocationの非alias証明ではない |

source SHA256:
- canonical one-root fixture: `8c040d74c16fd3a72c98124dbff1f087e475eba0cb8e60cb6da1c6244f979fd2`
- P278 registered source: `c092287c1f4e701ed50016168a3e7980900369b4728b2b3de10b904dfe33bd7c`

F49の36-source runnerは今回再実行していない。0–5成功world、TreeFour/Change/Reset、refusal/refund、general call/body inference、P284 full-source parserの改善も扱わない。

## ONE minimal mapping attempt と first missing interface

試した最小の対応は、実successのR ordinal/raw value ID/rangeをaccepted `BackingRegionId`/`ClaimId`/`Extent`へ対応付け、そのrawを最初のrich `Has(...storage e)`とするものだった。しかし:

1. accepted Backing.WorldはliveRegions/abstract bytes/accessだけを持ち、Allocation valueの発行・origin・current constituentを持たない。
2. accepted Occupancy.Ledgerのscopeは**fixed accounting scope**であり、Allocation/deallocation authorityではない。
3. accepted Accountingのraw claimはそのRが**既にlive**であることを要求する。raw→slotはscopeを増やさず、initializeもpreexisting Rとpreexisting live Dを要求し、Worldを保存する。
4. C event fieldをLean recordへ転記するだけでは、real source execution/current value/clone-historyからのrelationを構成できない。AllocatorのC scalar/nominal equalityは、abstract bytes/non-aliasやunique semantic Allocation issuerのrefinementではない。

従ってこのmappingは**Aで止まる**。初期WorldへRを入れ、full Storageを最初から与え、外部`AllocMatches`/carrier/CanEndを仮定して成功扱いしない。F0 ValuePackageのopaque payload、F1 StructuredValueのcontent、Conditional.Allocationのfresh fact supply、RelocationのopaqueAuthority、FiveRootのclosed original descriptorにも、実sourceのAllocation issuer interpretationを発行する規則はない。

最小の未実装interfaceは、**実source allocator-successが、元identityを保持するWorld extensionと新Rのabstract bytes/access、full raw claim、一意のAllocation originをcurrent source-owned constituentへ発行することを関連付ける小さなrefinement/導入**である。元Rの解釈・logical size・fresh abstract bytes/non-alias・source value ownershipは実イベントから生産すべき義務であり、入力契約として供給しても「sourceから証明済み」とは数えない。

それには新しい補助relation/semantic introductionの検討が必要だが、今回は導入しない。sourceで選択済みの§3.2aのformal coverage不足であり、canonical coreが矛盾するという発見ではない。新たなsemantic authority ruleを選択する場合はUNSELECTED/Gate A–E reviewが必要。Bのfresh D導入とCのcomplete ordinary carrier persistenceは後段の未証明義務。

## accepted richだけで新たに証明したこと

`NewLang.Adjunct.OneBackingIssuerBoundary`、**10 theorem + 2 concrete ledger definitions = 12監査宣言**。

| 宣言 | actual accepted premise / 導出 |
| --- | --- |
| storage_requires_existing_backing | Accounting + Has(storage e) → e.regionがpre-Worldでlive。Hasは入力の既存claimでありissuance結論を仮定していない |
| into_slot_requires_existing_backing | Accounting + actual RawIntoSlot.sourceClaim → 同じpreexisting R |
| initialize_requires_existing_backing | actual Occupancy.RawInitialize.backing.evidence/region → preexisting live R。post-WF/full-range不要 |
| initialize_is_not_fresh_region_issuance | pre-WorldにR不在 → そのRへのactual RawInitialize不可。source allocator自体が不可能という意味ではない |
| conversions_do_not_introduce_region_scope | actual RawIntoSlot/RawEraseSlot.post_eq → 両post.scopeが元scopeと等しい |
| lastByteLedger / last_byte_split_raw | accepted full4 rawLedgerを3+1へ分けるactual RawSplit。OneBacking resultとは呼ばない |
| last_byte_accounting / last_byte_split_is_rich_wellFormed | preaccepted Accountingから正・fits・same R・disjoint・complete coverage、実post rich WellFormedを構成 |
| complete_accounting_does_not_make_each_storage_full | 両StorageのHas、全footprint保存、prefix≠full、最後のclaim length=1 |
| lostLastByte / losing_last_byte_breaks_accounting | last-byte claimを除いたcandidateのcoverageに矛盾。**許可されたsource discard/transitionではない** |

exact origins:
- F1/Occupancy/Model: `surviving_claim_requires_live_backing`、AccountingShape.scopeLive/inScope、Accounting.coverage、WellFormed。
- F1/Backing/Model/Lifetime: EvidenceValid、RawInitialize.evidence/region、`initialize_uses_destination_placement`、`initialize_produces_current_ptr`。
- F1/Occupancy/Claims: RawIntoSlot/RawEraseSlot、consumeOne、RawSplit、`split_consumes_source_and_produces_two`、`split_conserves_all_byte_responsibility`。
- F1/Occupancy/Range: `split_extents_disjoint`、Extent/Geometry。
- accepted Occupancy/Counterexample/Cycle/Fixtures: full four-byte raw state、`raw_state_wellFormed`。fresh issuerを仮定した新modelではない。

F49のactual initialization→typed root/inc/D/exact extent、wrong governing D、duplicate actual root claim、half-range destroy/erase controlを保持。新moduleはfull original extentを手入力してAllocationの結論を出さない。

## adversarial disposition

- genuine A_C vs B ptr/D_B: C source-useの既存F49拒否を保持し、今回actual raw requiring-useでもsame-region mismatchを観測。**accepted-richにはAllocation interpretation/use自体がなく、要求された完全なwrong-A release theoremは未証明。**
- half-range typed end/erase: F49 accepted concrete countermodelを保持。新3+last-byte例は全AccountingがWellFormedでもparticular Storage fullnessが自動で出ないことを示す。正しいOneBacking full issuanceの反例ではない。
- duplicate/lost Allocation/current carrier: C owned poisonsは拒否する。rich byte責任の一意性はsemantic Allocation/carrierの一意性と異なる。F49 CurrentWellFormedのopaque content discriminatorを保持し、架空のA interpretationを追加しない。
- reused address: 元backing incarnationとnumeric addressを分ける。clone間の整数一致をorigin対応として使わない。
- stale O/wrong D: accepted `initialize_reused_placement_does_not_revive_old_ptr`はactual rich initializationとused old incarnationを入力に拒否する。F49 `wrong_governing_domain_rejected`はactual destroyのDを拒否。**sourceからそのrich constructorを生成する橋は未証明**。
- mixed ordinary packet: pure transportを違法化しない。operational release requirementsとH1 product criterionを混同しない。
- lost original packet: last byteのlossはrich coverageで拒否できるが、Aだけのlossをrich byte stateだけから検出するAllocation predicateは存在しない。これはunderspecified refinementの境界であり、accepted/sourceの合法なamplification countermodelを主張しない。

## 検証・停止

baseline: `lake build` **801 jobs PASS**、全1780 declarations audit PASS。
candidate: **802 jobs PASS / 1792 = 1780 retained + 12 PASS**。
Lean4.34.1、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。
whitelistはpropext/Classical.choice/Quot.soundのみ。全new declarationsをauditし、既存scriptから12追加行を除くとbaselineと完全一致。accepted theorem statements/core rules、manifest/toolchain/CI/Compilerの変更なし。sorry/admit/custom axiomなし。

exact candidate headとdecoded GitHub CI logsはIssue51の一件のhandoffで記録する。13 probe controlsはC empirical evidenceであり、1792宣言のsource refinement theoremがあるという意味ではない。

**FORMAL-HOLE / first source Allocation-state interface。** Draft17.30に対する矛盾や新broad owner engineの必要性は示していない。完全なAが未成立なのでB/Cへ進まず、Issue51をOPEN、F PRをDRAFT/UNMERGEDのままCoordinationへ返す。self-merge、canonical変更、Compiler実装、他Track起動なし。

Draft17.31 Gate E MERGE HOLD、full five-node B native STOP、H1 PASS/FAIL UNDECIDED、historical H2・staged migration S1は別。

F ORIGINAL ONEBACKING RICH ISSUER: HOLD — FIRST ALLOCATION/STATE INTERFACE STILL MISSING
