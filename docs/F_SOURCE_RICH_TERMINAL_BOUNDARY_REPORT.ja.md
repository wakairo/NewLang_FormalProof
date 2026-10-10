# F #49 — source由来の二root terminalとaccepted rich意味論の境界

Track: F

**HOLD — 最初の未証明interfaceは、実際の `Some(OneBacking)` 発行結果を、元AllocationのBackingRegionとfull raw claim、source上のcurrent非Copy constituentへ結ぶrefinementである。** accepted F1の実際のinitialize/destroy/erase constructorから、typed root・heap incarnation・governing Domain・同じextentの回復は導出できる。しかしAllocation発行・値のregion解釈・deallocation、およびsource aggregate/callとの対応は、そのconstructorに存在しない。

凍結P sourceを実行して得た観測と、Leanで証明したaccepted constructor間の含意を分ける。新しい`Matched`、`TreeTwoAlreadyOwnsBoth`、元Allocationを選ぶ魔法のbitは導入しない。canonicalの安全性の反例、source soundness、完全なafter-A rich terminalの証明は主張しない。

## 固定authorityと手順

- FormalProof/main固定base: `08c8b8da4b9dbe5e125e4be0643bffb28294bfad`。
- Compiler/main固定: `b75baea96a644e68634baee383299b66981b3c62`、CURRENT_SPEC **Draft 17.30**。
- 凍結P #280 source/checker: `4bc6b690e87b4646596dfd460bea26e9a5d8dac5`。stacked #275 `059b85497862d1461688ec5c6212e5ee87adf94c` → #277 `8fcda9e07a05626038508427794e4599563cdf5b`。全部未merge実験。
- 未採用M #273 candidate: `f778eba116d1834cc79c0bef6f6c17051102049f`、Draft17.31 §3.2c / DI-015 PROPOSED。PはM279前のcandidate `e6b4e98d4f19ed03bdba9a63ff0e86d6b40dc0a2` で実験した点も保持。
- Issue #49、P278報告 `6095194945`、PR280独立review `6095216937`、Coord裁定 `6095241304`、#268 sync `6095254439`、F43/F47報告を確認。
- Process §2/4.2/6/7、Design Decision Procedure、canonical §3.2/3.2a/3.2b、13.4/13.5/14/18.1a–c/18.2–18.8とcandidate §3.2cを照合。DI-011–014は既存closed evidenceのまま、DI-015は未採用。
- **Historical design audit: N/A — 新しいsource/API/core ruleの選択を行わない、既存accepted constructorの境界に関する補助証明・実験照合のみ。** §4.2のfaithful proof除外を適用。新しい選択にはCoordinationの独立履歴reviewが必要。
- Compiler checkoutのtracked変更なし。accepted Lean module、whitelist、toolchain、manifest、CIを変更しない。F49専用branchのAdjunctとreport、import、audit追加のみ。

## 実sourceから独立に確かめたこと

P snapshotを証明の入力にせず、凍結source/checkerを別checkoutで読む・buildする・再実行することから開始した。

`experimental_transitive_returned_whole.nl` のSHA256:
`c092287c1f4e701ed50016168a3e7980900369b4728b2b3de10b904dfe33bd7c`。

このsourceは五つのnested `try_allocate_one<Node>`、各SomeのOneBacking whole destructure、raw→slot→Domain→initializeを実行する。Bのlocal Domain loanとfield writeを閉じ、純粋なnamed `assemble(receiver,tail)` が返した `adopted` を保持する。A,C,srcのdestroy/erase/finalize/deallocate後に、一つの `finish_two(adopted)` を呼ぶ。これはP281の完全four-detach/two-adopt sourceではなく、P278の二member terminal sourceである。

```newlang
fn assemble(first:LiveRoot, second:LiveRoot)->TreeTwo {
    let combined = TreeTwo { root:first, child:second };
    return combined;
}
fn finish_root(ticket:LiveRoot)->unit {
    let LiveRoot { p, a, d } = ticket;
    let empty = loan_exclusive_read(d) { |ending| destroy(p, ending) };
    let full = erase_slot<Node>(empty);
    finalize_domain(d);
    deallocate(a, full);
    unit
}
fn finish_two(whole:TreeTwo)->unit {
    let TreeTwo{root,child}=whole;
    finish_root(child);
    finish_root(root);
    unit
}
```

hostにはCMake/LLVM23 toolchainが無かったため、**CMake全profile/LLVM smokeを実行したとは主張しない**。実際にLLVMへlinkしない三targetのCMake source listを使い、GCC14.2.0、C17、-O0/-g、-Wall/-Wextra/-Wpedantic/-Werror、三default-OFF opt-inを明示して、未変更の `newlangc` / `transitive_terminal_evidence` / `captured_closure_test` をbuildした。後者は既存malloc/realloc/calloc wrap付き。既存36-source runnerをCLI二回、owned observation/closure検証付きで再実行し、**全source SHA・分類・診断・公開観測JSONが凍結P278記録と完全一致**した。これは独立再実測でありLean refinementではない。

| actual source | 独立再実測 |
| --- | --- |
| exact returned whole、after A/C/src | exit4 V1-BACKEND-UNSUPPORTED。member paths [1,0]、ptr R / Allocation R / D=[5,3]、heap roots=[57,31]、incarnations=[60,34]、current whole=124、donor=70、formal=83、live A/D=2/2、loans=0、release=[2,4,1,3,5] |
| p_B/D_B + genuine A_C | B write・ordinary returnを経て、actual finish_two(pair) bytes [13712,13728) でexit3 semantic P193-CALL-BACKING |
| p_B/A_B + D_C | actual finish_two(pair) bytes [13778,13794) でexit3 semantic P193-CALL-DOMAIN |
| independent dst + A_C / D_C | dst member自身のrequiring callでsemantic拒否。Bの成功で代用しない |
| mixed ordinary return、後で修復 | ordinary returnのptr R=[5,3]、Allocation R=[5,4]。requiring call前に正しく再partitionし受理/backend未対応 |
| H0 unrelated caller B + Copy dst link | core-safe/backend未対応、H1 result-member=false。returned pairはdst+Cであり、Bは別に合法に解放 |

全36件: 9 semantic accepted/backend unsupported、21 semantic reject、4 precision unsupported、1 profile unsupported、1 parser unsupported。Unsupportedを安全な拒否として数えない。branch/refund、第三wrapper、temporary argument、whole-record loanはこの有限実験のprecision/profile限界であり、rich theoremで救済していない。

Source checkerの根拠も読む:
- `allocated_node.c:nl_allocated_grant` → `raw_storage.c:nl_raw_apply(NL_RAW_ALLOCATE)` はfresh regionと同じregionのAllocation/full Storageを実際に作り、Some/OneBackingへ非Copy memberをmove-inする。
- `transitive_terminal.c:nl_two_root_definition` は二つの異なるmember pathと、それぞれ独立check済みのfour-step terminal bodyを要求する。formalに具体的heap/R/A/Dを生成しない。
- `semantic_check.c` のwhole destructureはaggregateをEndedにし、actual memberをLOOSEへ移す。type-only formalは別のsymbolic値である。
- `typed_owner.c:owner_relations` はcurrent heap root/incarnation、live governing D、`a.allocation_region == root.placement.region`、full rangeとcurrent carrierを独立検査する。
- `raw_storage.c` のdeallocateは実際のAllocation/Storage同region、full-rangeを検査して両値をconsumeする。

これらのC実装上のfactsを、同名のLean theoremが存在するという理由だけでaccepted-rich仮説に昇格していない。

## 三つの判断

| 判断 | 独立に確認した意味 | 未証明部分 |
| --- | --- | --- |
| I ordinary非Copy transport | pure assemblerは任意の実constituentを運ぶ。mixed-repaired正例は受理。rich whole takeはexact opaque contents/dependenciesを返す | actual allocation/domain constituentsのcontent解釈、全current binding/member carrierとnamed construct/returnのsource refinement |
| II operational original authorization | actual requiring callがAのsame R、D governing、typed/current ptr、full raw、loan/consumeを別々に検査。accepted rich destroyもwrong Dを拒否し、同じroot claimからexact extentを回復 | Cのactual source eventからaccepted rich constructor、Allocation identity→region解釈とrelease judgmentへの証明 |
| III H1 K_dst+K_B result | 特定sourceのone returned wholeがdst+Bを保持する公開観測。H0はこれに失敗してもcore-safe | source-derived wholeとaccepted rich worldを結んだこのproduct witness。full cJSON graph/nativeは未検証 |

pure assemble/returnにmatchednessを追加することはしない。

## Leanで本当に導出した11の補助証明

新module: `NewLang/Adjunct/SourceRichBoundary.lean`。namespaceは
`NewLang.Adjunct.SourceRichBoundary`。F47のFrame/Return/Matched/LocalCanEndをimportも使用もしない。

1. `initialize_derives_root_domain_region`: actual accepted `RawIntoSlot` と `Occupancy.RawInitialize` から、同じ元raw extent、typed claim、heap root/incarnation、Governs(D)、CurrentAccessPtr、placement Rを導出。元Aとfull-rangeは導出しない。
2. `destroy_recovers_exact_initialized_root`: actual initialization resultと同じcurrent root claimを使うaccepted destroyから、extent、heap root/incarnation、ending D、ptr tokenの同一性とexact slotを導出。MatchedやCanEnd tripleを前提にしない。**実constructor自体のapplicability/ceはsourceから導出されていない**。
3. `destroy_erase_preserves_exact_claim`: actual rich destroy/eraseからexact raw extent、全byte責任、backing worldの保存と旧root/slot claimの消費。
4. `full_recovery_excludes_other_claims`: 初期extentがfullであるという**明示したgrant側の外部義務**が実際に満たされれば、accepted Accountingから同regionの別active claimを排除できる。Allocation/deallocateをmintしない。
5. `wrong_governing_domain_rejected`: accepted rich destroy自身の `domain_matches` による拒否。
6. `known_call_rejects_wrong_allocation_region`: accepted KnownCall adjunctのregion拒否。ただしargumentsの別々のallocationRegion/bindingをsourceから対応付ける証明ではない。
7. `current_wellFormed_does_not_interpret_installed_content`: 全installed opaque contentを任意に替えた状態もCurrentWellFormedになる。**WFだけからAllocation payloadのoriginを推論するadapterに対するdiscriminator**。合法なsource mutationを示すものではない。
8. `accounting_rejects_duplicate_root_claim`: 同じnonempty extentに二つのactive root claimsを置けばaccepted Accountingに矛盾。opaque sourceの二packetを二claimとして解釈する橋は別途必要。
9. `initialization_does_not_issue_a_domain_from_empty`: rich initializeは既にliveなDを要求し、empty semantic stateからsourceのlifetime_domain()を代行しない。
10. `rich_whole_take_preserves_value_and_domain_carriers`: actual accepted FixedLifetime.RawEndRootからexact structured valueを返すこととdomain carrier tableの保存。表の保存はsource memberへのcarrier再配置証明ではない。
11. `accepted_typed_cycle_does_not_imply_full_raw`: **既存accepted richの具体的countermodel**。四byte regionの二byte typed rootを合法に終了/eraseすると二byte rawだけが戻り、残り二byteは別claimのまま。typed/current root + 正しいD + 成功destroy/eraseだけではfull-range releaseは導けない。

### accepted lemmaのorigin

- F0/Lifetime: RawInitialize.target_after、initialize_creates_governing_relation、RawDestroy.domain_matches。元typed incarnation・Dはconstructorから導出される。
- F1/Backing/Lifetime: initialize_produces_current_ptr、RawInitialize.region、RawDestroy.token/current、destroy_ends_placement_not_backing。
- F1/Occupancy/Lifetime: initialize_consumes_slot_and_preserves_exact_responsibility、destroy_consumes_root_and_returns_same_slot、destroy_conserves_byte_responsibility、destroy_does_not_end_backing。
- F1/Occupancy/Claims/Conversion/Model: erase_slot_consumes_empty_exact_range、erase_slot_conserves_all_byte_responsibility、erase_slot_step_of_raw、nonempty_claim_cannot_be_covered_twice、full_region_storage_excludes_outstanding_subclaim。
- F1/Occupancy/Counterexample/Cycle: destroy_is_legal、erase_slot_is_legal。半region countermodelは新しいblessed五root recordではない。
- F1/StructuralValue: CurrentWellFormedとopaque content、FixedLifetime.take_returns_exact_value / end_preserves_domains。
- Adjunct/KnownCallProofs: entry_rejects_wrong_allocation_region。current Allocationのregion解釈まで証明したとは言わない。

半region例は**exact-size OneBackingの正しいP sourceの反例ではない**。canonical §3.2aのOneBacking full grantを本当にrefineすれば除外される。弱いrich仮説だけからfullnessを足す推論を反駁し、その最初の必要interfaceを特定する。

## 最初の欠けたinterfaceとstop

accepted F0 ValuePackageはpayload/authority algebraを意図的に省略する。F1 StructuredValue.contentはopaque Natであり、Allocationのsemantic interpretationではない。F1 Backing.World/Occupancy.Ledgerはbyte/claim accountingを持つが、Allocation value issuance/region association/deallocationを持たない。F1 Conditional.Allocationという名前はfresh fact/occurrence supplyであり、Backing allocation authorityではない。F1 Relocation.PackageData.opaqueAuthorityもAllocation refinementではない。

従って最初に必要なのは、実際のsource allocator successをaccepted rich initial stateへつなぎ、**同じOneBackingが発行した唯一のAとfull Storageのoriginを対応付け、その解釈をordinary source-current member carrierへ保つ小さなrefinement**である。F0 domain creationも別の欠けた導入境界。その後のconstruct/destructure/caller→callee→return→two terminal member paths、local vs heap incarnation、scope conflict、current domain-value borrow、exact nonDiscardable exitsのsimulationも未証明。今回はfirst small missing interfaceで止め、新owner engineやaccepted core ruleを足さない。

wrong A_Cをaccepted richのdeallocation judgmentで拒否するという完全な要求は、**そのAllocation judgment自体とsource interpretationが未実装なので未証明**。wrong Dは既存rich constructorで拒否できる。KnownCall adjunctのregion equalityにA_B/R_Bを手入力して、この違いを隠すことはしない。

## after-A、failure、negative controlの境界

P再実測の順序はA(#2),C(#4),src(#1),B(#3),dst(#5)。元B/dst heap incarnationは移転前後不変、current wholeのlocal placement/incarnationとは別。accepted F43の旧headLive(A) terminalは引き続き拒否され、F47のdst/B別viewとprimitive cleanupは既存researchとして保持。新moduleはそれらをsource-derived call証明へ変換していない。

Pのpublic closure validatorは0..5 success worldsを実際のsource traceから確認する。元grant/freeの列は0:none、1:src、2:A/src、3:B/A/src、4:C/B/A/src、5:after-A順序[2,4,1,3,5]。Noneに見えない六番目のgrantを与えていない。これをaccepted allocator初期化の六world theoremとは主張しない。一般refusal/branch/refundはPのprecision限界、source/rich affine exitも未証明。

negativeにはwrong A/D（Bとdst独立）、duplicate A/D/member、consumed donor/result、live D/H loanを跨ぐmove、stale B/dead A pointer、wrong raw terminal、lost member、wrong world/source/bodyのowned poison境界がある。今回36-sourceを再実行した範囲と既存P33 poisonの報告を区別する。**33 poison/OOM sweepsを今回新たに全部再実行したとは主張しない。** borrowed-fieldのrich current-fact blockerはaccepted F47/F1にあるが、actual source local loanへの依存生成は未証明。WorldIdの数値一致・global ledger・Copy linkをcurrent source ownerと同一視しない。

## 検証・裁定への提案

baseline `lake build` PASS 800 jobs、audit PASS 1769。
candidate `lake build` PASS 801 jobs、audit PASS **1780 = 全1769 retained + 上記11**。
standard whitelistは `propext`, `Classical.choice`, `Quot.sound` のみ、project sorry/admit/custom axiomなし。
Lean4.34.1 / mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。
exact candidate headとGitHub CI/logはIssue #49の一件のhandoffへ記録する。

**FORMAL-HOLE / source-to-rich interface。canonical source選択に対するHOLDを維持する。**
Pの有限source resultはpolicy-neutral Draft17.30の既存Allocation/Domain/nonCopy/operational-release規則と整合する範囲の証拠であり、新source admissionやgeneral call soundnessを選択しない。mixed pure return禁止やH1 product条件のcore-law化は不要。新しい広範なcore ruleの必要性も安全性の穴も実証していない。

Issue #49と上位#268は独立CoordinationのためOPEN。F candidateはDRAFT/OPEN/未merge。
canonical変更、Compiler実装、self-merge、他Track起動を行わず停止する。
full cJSON native STOP、Draft17.31 Gate E MERGE HOLD、North Star H1 PASS/FAIL UNDECIDED、historical H2は別。

F CJSON-B-STATE-1 TRANSITIVE ORIGINAL RICH ADAPTER: HOLD — SOURCE/ACCEPTED RICH INTERFACE STILL UNPROVED

