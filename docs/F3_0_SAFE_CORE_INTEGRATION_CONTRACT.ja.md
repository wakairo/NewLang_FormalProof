# F3.0 — Bounded Safe Core Integration Contract

Track: F

**Disposition: F3.0 CONTRACT READY FOR REVIEW**

本書は [Issue #22](https://github.com/wakairo/NewLang_FormalProof/issues/22) の設計裁定である。F3.0-pre [#23](https://github.com/wakairo/NewLang_FormalProof/issues/23) の CLOSED 後の再開指示を適用する。ここに記す global theorem、checking judgment、control/function adapter は**実装予定の contract**であり、既に Lean で証明された global theorem ではない。今回は documentation のみを変更し、F3.1 を開始しない。変更履歴は Git を正とする。

## 1. Authority、再開地点、validation

最初に Compiler main の `docs/NewLang_Project_Development_Process.md` を確認した。F-track は canonical を都合よく補わず、finding と review/closure を Issue 経由で Coordination に返す。

| Authority / evidence | 本 contract の確認地点 |
| --- | --- |
| Compiler main | `eda75ad09a73cacd0a78d1a0496aa0a86bd77a32` |
| Compiler `docs/reference/CURRENT_SPEC.md` | `NewLang_v0_spec_Draft17_17.md` |
| FormalProof main / base | `70aae8b9d945db7808f666e58fa31aa4dc9ef000` |
| Semantic Sync [Compiler #99](https://github.com/wakairo/NewLang_Compiler/issues/99) | CLOSED / SYNC PASS |
| M9.15 [Compiler #100](https://github.com/wakairo/NewLang_Compiler/issues/100) | CLOSED、NEXT = F3.0 |
| F0–F2、F3.0-pre #23 | reviewed / merged / CLOSED |
| #22 再開裁定 | [Coordination handback](https://github.com/wakairo/NewLang_FormalProof/issues/22#issuecomment-6028837854)、UNBLOCKED / RESUMED |
| baseline `lake build` | PASS、773 jobs |
| baseline `bash scripts/check-proofs.sh` | PASS、985 declarations |
| Lean / mathlib | `leanprover/lean4:v4.34.1` / `d13f23b723b8a846827a245b89c10fc7d3f11612`、変更なし |

Draft 17.4 は historical local snapshot。current authority は上記 Compiler main の Draft 17.17 であり、本作業では canonical、Lean source、proof audit、pin、manifest、CI を変更しない。許可する axiom dependency は `propext`, `Classical.choice`, `Quot.sound` の既存 whitelist のみ。

関連する canonical rule は Draft 17.17 §13.5a / §13.5b（surviving dependency / place effects / cyclic header）、§14.1–6（lifetime / domain）、§17.4（current-value update）、§18.1–8（ordinary call / transfer / exit）、§23.1（raw responsibility）、§26.4 / §26.6–8（static sum capability / occurrence）です。source loop grammar の追加は今回の semantic integration target ではありません。

### 解消済みの interface と残る scope

元の F3-IF-1 は、occurrence dependency を消す erasure から rich lifetime legality を逆算してしまう interface gap だった。#23 の [report](F3_0_PRE_SUM_LIFETIME_ADAPTER_REPORT.ja.md) と [`SumLifetime.lean`](../NewLang/F3/Memory/SumLifetime.lean)、[`Proofs.lean`](../NewLang/F3/Memory/Proofs.lean) により次が bounded scope で利用可能になった。

- rich `take` / `destroy` は raw candidate、pre invariant、explicit `SurvivorGuard` から post invariant を導く。post WellFormed を入力に要求しない。
- root current fact、active occurrence、payload current fact は終了し、returned package の dependency data は変わらない。take と destroy の remaining carriers が異なる。
- 一つの live root / region / responsible root claim を同 extent の slot claim に変換し、exact responsibility を保存する。外部 loose survivor は許す。
- rich legal lifetime step から coarse legal step への sound direction は証明済み。`coarse_legal_take_does_not_imply_rich_legal_take` は逆向きを反駁する。

**裁定:** first Safe Core の rich sums は already-live/preinitialized とする。bounded rich take/destroy はこの adapter をそのまま使用する。flat initialize は F1.4 evidence を使用する。rich sum initialize、rich by-value destination/root binding は later **FORMAL-SCOPE**。#23 は source ending の proof であり、destination start や sum parameter binding の proof ではない。元の gap を再調査・再 block しない。

## 2. 三つの claim と theorem property

- **Claim A:** この contract で定義する formal Safe Core soundness。
- **Claim B:** production acceptance と source meaning を formal core/checking judgment へ接続する refinement。future work。
- **Claim C:** lowering/backend execution が formal semantics を保存する simulation。future work。

A を証明しても B / C は成立したことにならない。

property の比較:

| 候補 | 裁定 |
| --- | --- |
| preservation only | primitive evidence の再利用には有用だが、invalid attempted operation の除外を表さない。補助定理にする |
| preservation + separately modeled no-fault | **base theorem family に採用** |
| progress / preservation | initial platform / representation contract と intentional zero-normal exit があるため、first theorem には採用しない |

予定する statement は次の形である。`E` は §10 の environment contract、`I` は initial resource/type/ownership contract、`Cfg` は control/frame と authoritative memory を持つ concrete configuration。

```text
WellCheckedCore(P, I, E)
∧ InitialSafe(I, E, cfg0)
∧ RawExecPrefix(P, E, cfg0, trace, cfgN)
-------------------------------------------------------------
GlobalSafe(cfgN)
∧ NoModeledSafetyFault(trace)
∧ ResidualChecked(P, cfgN)
```

`RawExecPrefix` は arbitrary finite prefix。raw success と fault attempt を含み、post WF や `LegalStep` を前提にしない。fault に入った trace も relation 上は表せるので、no-fault 部分に内容がある。補助 family は `checked_raw_step_preserves`、`checked_attempt_cannot_fault`、`selected_arm_preserves`、`checked_call_return_preserves`、`checked_loop_prefix_preserves`、terminal normal/Return の `exit_contract_sound`。名称は prospective であり既存 Lean declaration と混同しない。

`GlobalSafe` は §5 の独立した state invariant。`NoModeledSafetyFault` は `¬WellFormed` の別名ではなく、次の具体的 fault event が trace に出ないこととする。

| Modeled fault event | 検出対象 |
| --- | --- |
| `StaleAccess` / `InvalidAccess` | exact incarnation/domain、read/write/representation/backing evidence の不足 |
| `DeadSurvivorDependency` | invalidation 後に残る exact value/domain/occurrence/payload fact dependency |
| `AffineViolation` | duplicate/lost package carrier、消費後の再使用、non-Discardable discard |
| `ResponsibilityViolation` | scoped bytes の責任欠落/二重化、wrong extent、inactive claim 使用 |
| `InvalidLifetime` | vacant/live applicability、ending authority、historical identity reuse |
| `ScopeEscape` | ended callee/iteration/local identity に依存する returned/surviving package |
| `InvalidControl` | 未宣言 callee/arm/edge、wrong typed return、Continue/Break/Return の混同 |

fault は選択した抽象 semantic model の safety violation attempt であり、hardware fault、OOM、raw byte validity、全ての undefined behavior を列挙したものではない。内部 concrete carrier/ledger の保存は preservation theorem が担い、fault event の排除は checking rule と adapter が担う。termination、liveness、allocator 成功、loop の normal exit、全 v0 safety、production/compiler correctness は主張しない。

## 3. Exact first Safe Core subset

有限 program、有限 static type/layout/function table、有限 explicit memory scope に限定する。capsule registry は実行中に増減せず、所有 namespace の retired identities も history に残す。runtime finite prefix の長さと fresh nominal identity の値には固定上限を置かない。source parser grammar を target にしない。

**Composition bound:** finite sealed memory capsules を使用し、一つの capsule は一つの profile に属す。各 operation/function/loop は明示された capsule を扱う。profile 間で package/carrier を transfer せず、dependency は同 capsule 内で閉じる。region byte footprint、nominal identity ownership、domain ownership は capsule 間で disjoint。cross-capsule alias、dependency、domain transfer、overlapping placement は first subset の checking で reject する。この制限は NewLang semantics ではなく first formal theorem の precision bound である。

| Included item | Exact bound / 理由 |
| --- | --- |
| ordinary named function、direct call | finite monomorphic signatures、acyclic call graph。caller/callee は同じ capsule の authoritative memory を共有し、control/local ownership frame を push/pop する。actual body を検査する |
| lexical flat binding / value transfer | flat profile の slot-backed initialize と take による source-end / destination-start。non-Copy carrier を move し、dependency data を保存。implicit rich destination initialize は含めない |
| fixed aggregate/current-state | F1.1 の finite fixed support の semantic-only profile。root/child replace/store、same/distinct swap。physical typed-layout embedding や aggregate lifetime start/end は含めない |
| closed sums | F1.2 root-level opaque payload の rich profile。whole/payload replace/store、same/distinct whole swap。nested sum、fixed-child 内への sum embedding は含めない |
| rich lifetime ending | #23 の one-live-root / one-region / one-active-claim の take/destroy、loose external survivors。複数 live root の rich ending は含めない |
| flat raw/typed memory | F1.3/F1.4 の geometry/layout、Storage/slot split/merge/conversion、flat initialize/take/destroy、flat replace/store/swap を coherent adapters で使用 |
| LifetimeDomain | flat profile の exact domain carrier transfer/finalize と surviving `DomainLive` guard。終了前に governing roots と retained capabilities を閉じる。rich/fixed profile では domains を live のまま frame する |
| ptr/ref | exact ptr provenance/token、operation-local acquisition/use、explicit backing/access evidence。stale token を fresh root へ retarget しない。persistent ref-valued lexical binding/return/join は除外 |
| dependency-carrying values | actual package data にある exact ordinary/rich facts。initial contract や existing value transfer による occurrence-dependent package を含み、第二 dependency system を作らない |
| finite control | Seq、If(Boolean)、closed finite Match(current variant observer)、Return。Match は borrowed/consuming frontend ではなく、payload capability を新規発行しない arm selection |
| bounded loop | F2 の zero/one affine parameter、one captured availability、one mutable outer Copy place、各 Continue/Break/Return class 最大二 edge。single non nested loop、§8 の flat adapter/frame 制約 |

rich profile では一つ以上の finite preinitialized roots に対する value updates/swap は使用可能だが、take/destroy node は #23 の single-root configuration に限る。sum root は ordinary function の caller-owned access operand として参照できる。rich by-value parameter を新しい root に bind する call、rich local initialize は不可。sum take の result は loose semantic value として残す/terminal result に渡せるが、新しい rich binding を暗黙に開始しない。

| Exclusion | 理由 / safety claim への影響 |
| --- | --- |
| rich initialize、rich by-value parameter/local destination | 再開裁定の later FORMAL-SCOPE。source ending adapter を destination proof にしない |
| arbitrary aggregate/sum embedding、nested occurrence | existing singleton/root-level physical evidence を超える |
| full borrowed/consuming match、payload ref issuance、persistent ref future-use、complete P7 ref-result alternative joins | acquisition/value-dependency evidence と full source ref checking を区別。ref safety claim は operation-local に限定 |
| cross-capsule transfer/dependency/alias、overlapping region scopes | authoritative ownership/frame の first bounded decomposition を保つ |
| nested-loop composition、recursive call SCC | F2 の one-loop evidence と acyclic call induction を超える。NewLang 全体がこれらを禁止するとは言わない |
| callable/generic/Array-span-range | 新しい semantic surface / interfaces が必要 |
| arbitrary unchecked、dynamic-container privileged bridge、FFI | explicit verified adapter のない memory mutation を oracle 化しない |
| modules/linking/concurrency、frontend/parser/diagnostics、LLVM/backend、self-hosting | claim B/C または別 execution model |
| F1.5 relocation | §11 の optional extension。base の必須 operation/field にしない |

## 4. Architecture — adapter/refinement network を選択

| Architecture | 判定 / blast radius |
| --- | --- |
| A unified giant state | 不採用。全 historical kernel の state/proof を再構成する必要がある |
| B independent product + projections | 不採用。複製された package/root/ledger owner が異なっても各 component WF は成立し得る。coherence 未証明の product は soundness 根拠にならない |
| **C adapter/refinement network** | **採用**。profile ごとに authoritative memory を一つ持ち、view は derived。新規 proof は control/checking・frame・adapter seam に限定 |
| D new architecture | concrete project evidence 上 C より小さい必要性がないため採用しない |

```text
Declarative WellCheckedCore(P, initial contract)
                   | subject reduction / selected control
                   v
Cfg = control + call/local ownership frames + finite sealed capsules
     | capsule registry: disjoint ownership, exact loose-frame correspondence
     |
     +-- Flat authority: Occupancy.State
     |       -> Backing.FlatState -> F0.State       (derived views)
     +-- Fixed authority: F1.CurrentState            (semantic-only)
     +-- Rich authority: Occupancy.SumState
     |       -> Backing.SumState -> Conditional.State
     |          +-- #23 rich take/destroy (authoritative guards)
     |          +-- erased F1.1 / F0 WF sanity        (one-way)
     |
     +-- F2 header view of one Flat capsule + literal unchanged side frames
     +-- optional F1.5 adapter, outside base

Forbidden: erased coarse legality -> rich legality
Forbidden: independent views each allocate/own the same package or byte range
```

capsule registry は name/ownership partition と view selection の metadata であり、新しい allocator/runtime object requirement ではない。data owner は各 profile の既存 state。call frame はその中の loose carrier/claim を**指す**もので、第二 carrier を追加しない。frame 所有の loose package の bijection、unbound expression/terminal carrier との排他、installed carrier との非重複を `FrameOwnership` が検査する。history と type table の owner も capsule に一つ。view への mapping は injective identity relation を維持し、fresh supply は所有 namespace と history を満たす。

capsule ごとの local WF に加え registry disjointness、dependency locality、frame-carrier correspondence、control typing が必要。これらを `InitialSafe` で確立し、adapter の frame lemmas から保存する。product component WF だけを initial theorem premise にしない。呼出しに応じて caller/callee memory をコピーせず同 authority 上で ownership permission を分割する。

既存 public definition/theorem statement は維持する。F0 state は flat profile の semantic view。rich profile の erasure は precision-losing sanity view であり、execution の authority ではない。fixed semantic-only profile を arbitrary physical aggregate と同一視しない。必要な新規 adapter proof は §14 に列挙する。

## 5. Global invariant bundle と F0–F2 mapping

分類 G = global base、P = local pre condition、Q = local post condition、X = extension、H = proof-only ghost、O = outside first theorem。

| Evidence / module | 分類 | Integration obligation |
| --- | --- | --- |
| F0 WellFormed carrier/place/incarnation/package uniqueness/presence | G | profile WF、capsule identity disjointness、frame ownership を合わせる |
| F0 live domain / domain carrier coherence | G | live relation を actual authority に一つ持つ。finalize は survivor guard と authority を P に持つ |
| F0 / F1 exact dependency validity | G/P/Q | actual surviving carriers の deps が actual rich/ordinary LiveFacts に含まれる。invalidation footprint と survivor conflict は P、unchanged dependency data は Q |
| usedValueFacts / usedIncarnations / usedOccurrences | H/G | live identities recorded、historically fresh supply は P、history monotonic は Q。runtime history set を要求しない |
| F0 Reference exact token / acquisition / stale rejection | P/Q | operand の exact location/incarnation/domain と access evidence。persistent ref scope/join は O |
| F1.1 fixed child/current consistency | G/Q | layout/support/incarnations を保持し affected current facts だけ freshen |
| F1.2 occurrence shape/uniqueness/recording | G | place-owned conditional identity。whole reset、payload preserve、same no-op、distinct fresh は Q |
| F1.2 surviving occurrence/payload dependency | G/P/Q | value transfer は identity transfer/retarget をしない。whole store と replace の survivor 差を P へ反映 |
| F1.3 backing/placement coherence | G | active typed root の exact placement/live region。geometry/alignment/representation/access は P |
| F1.3 authority/access non-amplification | Q | operation が入力以上の read/write authority を発行しない |
| F1.4 Accounting / Storage/slot/root claim | G/Q | 明示 scope の complete/disjoint responsibility。exact range/active claim/applicability は P、whole scoped footprint conservation は Q |
| #23 rich end | P/Q | ended root/current/occurrence/payload facts、read take vs Discardable destroy、single claim conversion、post SumWF を guard から導く |
| F1.5 relocation | X | separate extension invariant、conservation/freshening/owned-claim adapter |
| F2 H / post-fixpoint | P/H | entry coverage + all reachable Continue transfers の static certificate。concrete header は runtime view |
| F2 affine/exact captured availability | G/P/Q | call/local carrier correspondence を header へ写す。exact availability は widening しない |
| F2 blockers / control exits | P/Q | ScopeClosed / exact facts、Continue/Break/Return 分離、zero-break は zero normal result |
| global call/control/capsule coherence | G | 新規 execution layer。既存 local proofs の conjunction だけでは得られない |
| full source checking / production/backend semantics | O | §12 の別 refinement |

`GlobalSafe(cfg)` は applicable profile invariants + registry/frame/control coherence + active capability/operand constraints。heap 全体を表す invariant ではなく explicit owned scope を表す。pending return package も survivor に数える。caller に隠れた package を無視した callee-only dependency check を禁止する。

## 6. Operational semantics と non-vacuous checking

**statement/control small-step + raw atomic primitive transition** を採用する。core AST は operand identity/type と Seq、If、Match、Call、Return、Loop、Continue、Break、primitive nodes を持つ有限 syntax。source expression/parser/compiler IDs の encoding ではない。Bool/variant observation は side-effect-free。非決定的 fresh choices は歴史と所有 namespace で制約される。

- Seq は一つずつ node を実行する。If/Match は runtime observer に対応する一 arm のみ実行する。
- Call は actual body の control を push。Return は result/ownership transfer と callee exit obligations を行い caller continuation へ戻る。
- Loop は concrete header/body/edge transition を実行する。H や static join を concrete memory として実行しない。
- primitive attempt は applicability / access / survivor / responsibility 違反なら明示 fault event を出せる。success candidate は既存 Raw relation に対応させる。swap/store の atomic candidate を replace の連列に置換しない。
- `CoreRawStep` の definition に post GlobalSafe、post local WF、static checking proof は埋め込まない。

**Checking Option 1（declarative derivation）を採用**する。proof-carrying AST は Option 1 の serialization として可能だが別 trust assumption にしない。Option 3「各実行 step が Legal」は拒否する。

`CheckStmt Γ S stmt Outcomes` の `S` は finite symbolic resource state / exact dependency-and-identity relations、`Outcomes` は Normal/Return/Continue/Break の分離した alternatives。type、ownership、access provenance、affected fact support、全 survivor conflict、discard/static type、scope closure、claim conversion を rules の具体的 side condition にする。unknown value は許すが exact availability と possible blocker を忘れない。fresh fact/occurrence/incarnation は symbolic binder と historical freshness condition を持ち、具体値を静的列挙しない。

program 入口で initial contract と各 actual function body の derivation を一度証明する。`Rep(S,cfg)` で concrete resource/identity/dependency を対応付け、step ごとの subject reduction が dynamic guard と new `Rep` を**導出**する。source checker algorithm の decidability/completeness は要求しないが、checking derivation の rules と witness は有限で検査可能にする。

```text
CheckPrimitive(Γ,S,op,Snext) ∧ Rep(S,cfg) ∧ GlobalSafe(cfg)
   -> dynamic applicability/access/freshness/survivor/resource guards
   -> Raw candidate has local WF + framed registry/control invariants
   -> Rep(Snext,cfgNext) ∧ GlobalSafe(cfgNext)
```

既存 `ReplaceStep` / `StoreStep` 等の post-WF projection theorem をこの第二 implication の proof と呼ばない。必要な新規 bridge は raw candidate 上で guard と invariant clauses を証明し、最後に legal Step を構成する。#23 はこの方向の既存 evidence。`CanWrite`, `TypeCompatible`, `ce` を `True` と固定したり、全 transition 安全性を含む proposition として入力したりしない。ordinary capability context から導く部分と §10 の具体的外部 contract を区別する。

## 7. Minimum function / finite control scaffold

function は monomorphic signature と actual core AST body。call graph の rank が strict decrease する acyclic direct call のみ。opaque `SafeBody` / `SafeCall` を置かない。

| Function interface | Checking / execution contract |
| --- | --- |
| signature | finite flat type、Copy Bool/unit、owned flat value operand、caller capsule access operand、result type と ownership/effect relation（rich profile の loose result を含む）。generic/callable なし |
| parameter transfer | flat owned input は caller loose carrier を一度 consume し explicit callee slot を initialize。source root から渡す時は take が source を終了する。Copy は明示 Copy 型のみ。rich root access は caller root を移転しない、rich by-value 新 root は禁止 |
| frame | caller memory は同じ authority 上に残り全 survivor deps も見える。callee local claims/packages は registry の排他的 subset。caller loan は operation-local acquisition に使用し、callee を lifetime-ending authority と混同しない |
| callee body | body derivation を signature pre-symbolic state から検査。call site は type/ownership/substitution/alias restrictions と expected effects を照合 |
| return | returned package は loose carrier 一つとして caller expression/result に transfer。dependency data unchanged。flat destination binding は別 initialize。normal fallthrough と Return を混同しない |
| callee exit | callee live locals を明示 take/destroy、残る slot を caller resource frame へ返す。implicit unrestricted cleanup を仮定しない。returned/caller-survivor deps は ended local/iteration/domain fact を参照できない |
| caller-visible post | mutation された current facts、survivors、history、claims を actual same authority から反映。caller 旧 dependency を callee frame 外だから無視しない |

callee へ access operand を渡すことは source-level persistent ref parameter の full proof ではない。core の scoped exact access contract であり、source correspondence は B が扱う。ordinary flat owned parameter/return と rich preinitialized root の更新は含むが、任意 NewLang signature を含むとは言わない。

finite If は両 statically reachable arms を検査する。finite Match は nominal closed variant table の全 reachable cases と exactly one runtime variant を対応付ける。arm selection は fact invalidation/occurrence generation を行わない。payload-dependent value が存在する state では actual deps をそのまま保持する。payload 参照の新規発行や consuming-match lifetime start/end は first Match に含めない。

normal-state join は alternatives を含む static relation で、runtime は一つの具体 state。affine availability が違う normal branches を可用として join しない。fact/occurrence identity が分岐で違う場合には disjunctive alternatives と exact blockers を保持する。returned ref-valued alternative joining は除外。Return/Break/Continue は normal join に入れず separate effect にする。

予定 theorem:

```text
AllReachableArmsChecked(S, arms, outcomes)
∧ Rep(S,cfg) ∧ RuntimeSelects(cfg, arm)
-> arm has matching checked derivation
-> selected execution preserves GlobalSafe and its classified exit contract
```

zero-normal branch/function は Return-only と表せる。continuation の normal state を捏造しない。finite bounded call/branch の witness を §15 で要求し、statement の空集合だけを対象にしない。

## 8. F2 loop adapter

F2 の [`Model.lean`](../NewLang/F2/Model.lean)、[`Abstract.lean`](../NewLang/F2/Abstract.lean)、[`Reachability.lean`](../NewLang/F2/Reachability.lean)、[`Exit.lean`](../NewLang/F2/Exit.lean) を変更せず reuse。F2.body は旧 kernel では transfer premise だったため、F3 は **actual checked core body execution** からそれを構成する。

exact first loop slice:

- one Flat capsule、one unchanged live outer Copy root/current fact、zero/one loop-carried affine loose value、one captured non-Copy availability。iteration binding は control ownership view で第二 package carrier ではない。
- body はこの slice の unchanged/transformed carry、outer Copy current-value mutation、finite If と explicit edge に限定。outer root lifetime/domain は固定。carry transform は explicit consumption/creation rule と fresh package identity を持ち、`Carry.transformed` 全体を oracle にしない。
- それ以外の同 capsule memory/claims と全 rich/fixed capsules は literal unchanged side frame。side-frame package deps が変更される outer current fact を含まないことを static frame side condition にする。これは blocker を削除する rule ではなく loop applicability を reject する rule。
- `publicFacts` は実際の stable local facts のみ。mutable outer place のどの VF も publicFacts へ入れない。rich occurrence atom を F0 fact に射影して LoopCarry を承認しない。rich/occurrence-dependent value を loop carry に含める generalization は later scope。

| Static evidence | Runtime adapter / derived result |
| --- | --- |
| entry `RepLoop` と concrete HeaderWF、entry ⊆ H | actual initial header の coverage |
| checked actual body、complete finite edge set | 各 runtime selected edge は supplied family の一つ。runtime fixture で bad edge を消さない |
| each Continue transfer checks header/affine/exact availability/fresh scope closure | body execution から before/after HeaderWF と ContinueFrame を導き既存 Continue relation を構成 |
| H inductive post-fixpoint、blocker-preserving widening | arbitrary finite Continue sequence の coverage theorem を import。Unknown は known blocker を消さず exact availability を保つ |
| separately checked Break / Return | actual exit に ExitWF/ExitFactsLive を導き、finite Break join のみ normal successor へ戻す。Return は function exit へ渡す |
| no Break cases | zero normal result。finite prefix safety は成立するが terminating/result witness を作らない |

`loop_prefix_adapter_sound` は F2 prefix を global authoritative flat state と unchanged rich side frame へ lifting する予定 lemma。H は runtime executablestate ではない。parameter 外 availability の違反、hidden iteration dependency、旧 outer fact を stable publicFacts へ追加する例、unsupplied second Continue、Return を Break へ混ぜる例を negative controls とする。

## 9. Raw/typed lifetime、sum、ref の adapter boundary

### Memory authority と lifecycle

```text
explicit live BackingRegion / scoped raw Storage claim
  -> exact split/merge / slot<T>
  -> flat initialize (write + destination + freshness)
  -> live typed root (same ledger responsibility)
  -> atomic replace/store/swap or take/destroy
  -> exact returned slot -> erase_slot -> raw responsibility
```

flat authority は `Occupancy.State`、rich authority は `Occupancy.SumState`。typed semantic root と root claim は同一責任の二つの記述で、第二 owner ではない。geometry/layout/alignment/positive static size は explicit contract。F1.4 `Accounting` と conversion/partition proofs を reuse し、raw→typed と typed→raw の candidate-specific post proof は new checking adapter が導く。flatF0 は projection、精度を失う rich erasure は state sanity に限定する。

rich sum path は **initial already-live root -> value updates -> #23 take/destroy -> slot/raw**。whole/payload value update は physical/ledger を frame し、typed static capability を保持する。same-variant whole update でも old occurrence を終了して fresh 再開始、payload-only は occurrence 保存、same-placeswap は exact no-op、distinctswap は fresh destination occurrence と unchanged package/deps。static sum-type Discardable を runtime variant の proxy で置換しない。take は returned package を survive させ、destroy は消費し、root/current/occurrence/payload fact への guard は actual remaining carriers へ適用する。

### Ref evidence audit

| Interface | Existing evidence / first theorem bound |
| --- | --- |
| exact PtrToken / CurrentPtr、wrong location/incarnation/domain rejection | F0 Reference machine-checked。F1 Backing は actual placement/access と non-amplification を保持 |
| current acquisition と read/write operation-local use | base に含む。checking から exact token と domain/access evidence を導く新しい control adapter が必要 |
| stale-after-take/destroy/reinitialize | existing machine-checked。stale provenance を持つ ptr 値の存在自体は fault でなく、invalid reacquisition/use attempt を reject |
| rich occurrence/payload dependency と no-retarget | F1.2 / #23 machine-checked。actual package data を使用 |
| payload ref safe issuance / ordinary persistent ref parameter-return / lexical future-use | canonical/production evidence のみで complete formal proof はない。first base から除外、点の acquisition theorem で代用しない |
| function-boundary package dependency transfer | new bounded flat call adapter の target。deps を保持し all caller/callee survivors を guard する |
| P7 complete ref-result alternative join | missing full formal interface だが first base では不要。ref-valuedjoin を除外して bounded precision を明示する。P7/P14 CLOSED を Lean proof の代用にしない |

persistent provenance は blocking dependency ではない。ptr 由来という理由だけで全 value へ OccurrenceFact を自動付与せず、dependency として明示された fact だけを global check へ入れる。

## 10. Unsafe / privileged / environment boundary

**Policy C（operation ごとに mixed）**を選ぶ。unchecked 全体を safe oracle にしない。

| Assumption / operation | Treatment |
| --- | --- |
| arbitrary `unchecked` | AST subset の外、WellCheckedCore derivation なし |
| platform address / backing provision | initial `E`に finite geometry、live backing、valid representation/alignment と owned footprint を明示。provision operation を任意 memory mutation として許さない |
| allocator / deallocator | general allocator 正しさ/成功なし。explicit provided region 内の claim conversion だけを証明。deallocator/external mutation は外 |
| representation / alignment | typed-layout/backing contract の predicate と保持条件を表示。ordinary type/size/access 由来の証明と external premise を区別 |
| write/read/stability/ending authority | exact capability context、domain/resource binding から local rule が導く。ending `ce` の外部部分が必要なら具体的 authority/representation contract に限定し theorem の E に露出。post-WF や body 安全性を含めない |
| dynamic-container privileged bridge / external effects / FFI | first base の外。新 bridge に proof obligation ができるまで assumed-safe action を入れない |
| environment mutation during execution | E で許された観測と fresh choice のみ。owned backing/liveness/dependency を任意変更しない |

E が偽なら theorem を production へ適用できない。E が「全 program safety」と同値になる定義は禁止する。static evidence を毎 step external oracle から補充する design も禁止する。

## 11. Relocation — optional extension

F1.5 は base に必須としない。extension の候補 statement:

```text
GlobalSafe(cfg) ∧ ExtensionRep(relocState, selectedRichCapsule(cfg))
∧ ExplicitRelocationInput(relocState, ...) ∧ RelocationSurvivorGuard(...)
∧ RawRelocation(relocState, ..., relocPost)
-> GlobalSafe(replaceSelectedCapsule(cfg, project(relocPost)))
   ∧ ExtensionRep(relocPost, ...) ∧ responsibility/history conservation
```

F1.5 `Relocation.State.accounted` を selected rich authority に対応させ、owned claims/persistent ptr annotations を既存値と coherent にする adapter が必要。source/destination overlap、fresh identity、unchanged dependency/provenance、whole footprint、other capsule frame を証明する。既存 legal relocation の post-WF projection だけで raw adapter を完成したことにしない。全 program へ relocation metadata を追加せず、first F3.1 では実装しない。

## 12. Production / backend refinement boundary

**B — future production/source refinement:**

```text
ProductionAccepted(source, artifact) ∧ SourceInBoundedSubset(source)
-> ∃ core I,
     FormalizesAs(artifact, core, I)
     ∧ SourceRefinesCore(source, core, I)
     ∧ WellCheckedCore(core, I, E)
```

`FormalizesAs` は型/キャリア/依存/制御/initial resources の対応。`SourceRefinesCore` は source execution と core results/effects の simulation を要求し、単なる artifact AST 一致ではない。fault、normal/Return、visible updates を観測に含む。unchecked/platform contract の相違も露出する。C production checker の現 acceptance から WellChecked を得る proof は未実装。formal core の subset outside なら A 適用不能。

**C — future backend simulation:** typed IR/machine execution が control/selected arm/call return、affine carrier、exact dependency identity、incarnation/occurrence freshness、authority/readwrite、placement/responsibility、observable effects を保存する必要がある。backend は semantic fact を address へ collapse したり stale identity を fresh destination へ retarget したりしてはいけない。machine fault を modeled core fault に対応付ける別 simulation も必要。MIR grammar、LLVM、lowering algorithm は今回設計・実装しない。

## 13. W1–W15 stress workloads と anti-vacuity

以下は contract-levelanalysis/acceptance target であり、今回新規 Leanwitness を証明したという主張ではない。

| Workload | Concrete handling / limit |
| --- | --- |
| W1 owns/updates/returns flat value | caller take → callee flat slot initialize → body replace/store → return take。self-current dependency は replace で reject、old-only discardable dependency は atomic store で消費可能。actual body derivation と survivor/claim frame を証明する |
| W2 LifetimeDomain end | flat finalize は ended DomainFact を列挙する。surviving package / operation-local evidence に DomainLive(D) が残れば checking が reject し、attempt は DeadSurvivorDependency。rich domain end は first scope 外 |
| W3 Storage lifecycle | 同 extent の raw → slot → flat initialize → take/destroy → slot → raw。各 adapter の Accounting/footprint 保存を chain。rich は already-live から ending 側だけ |
| W4 stale ptr | old token を保持して flat end → fresh restart した後、old token の acquisition/use は incarnation mismatch。ptr provenance の保持自体は禁止しない |
| W5 sum + payload ref | existing occurrence-dependent package を保持した whole variant reset は guard で reject。Match は variant observer。new payload ref issuance / full borrowed match は base 外で、完全な ref safety を証明したとは言わない |
| W6 direct call | 同じ authoritative capsule の current fact を callee が更新する。caller loose package の old-fact dependency も guard に残す。ended callee-local dependency を returned package へ逃がせない。sum の新 parameter root binding は除外 |
| W7 finite If | reachable arms を両方検査し、runtime は一 arm。unchecked な second arm があれば first arm の witness だけでは checking が成立しない |
| W8 Return vs normal | Return arm は caller return contract、normal arm のみ continuation join。all-Return なら zero-normal で、架空の normal state を作らない |
| W9 loop | checked concrete body から F2 Continue/Break/Return を導く。exact availability、affine carry、frame blocker を保存し finite prefix soundness を import |
| W10 zero Break | arbitrary finite Continue prefix の safety、normal result なし。Return は別 outcome。termination/result を存在量化しない |
| W11 recursive SCC | call rank derivation ができず excluded。acyclic subset の theorem は維持 |
| W12 unchecked | core node なし。initial environment contract に program safety 全体を隠す shortcut を拒否 |
| W13 relocation | extension adapter のみ。base checked program/execution に密かに追加しない |
| W14 production mismatch | 仮想 C checker が old-occurrence-dependent returned value を見落として accept。formal checking は reject だが、A から ProductionAccepted → WellChecked は出ない。B の failure |
| W15 backend miscompile | 仮想 lowering が old token/Occurrence を destination の fresh identity へ retarget。formal raw semantics と異なる trace なので A は machine execution を保証しない。C の failure |

拒否する bad architectures:

1. `WellCheckedCore := ∀ executed step, LegalStep`。post-WF を仮定しており checking→guard proof がない。
2. `GlobalSafe := reachable by safe transitions`。carrier/dependency/ledger/control の独立 property がない。
3. `SafeCall/SafeLoop/SafeUnsafe` の無制約入力。actual body/edge/authority contract を proof せず核心を oracle 化する。
4. 各 productview の WF だけ、または coarse legal→rich legal。owner coherence を失い、#23 の coarse-legal/rich-illegal counterexample に反する。
5. field/variant/runtime payload を Discardableproxy にする、unknown join で blocker 消去、caller frame を survivor から除外する。具体的 guard が変わる。
6. all-arms static join を runtimeboth-arms として実行する、Return/zero-break を normal state に混ぜる。control 意味を変える。
7. 全 memory/function/loop を除外し emptyprogram だけの global theorem にする。first subset は flatlifecycle・rich ending・fixed/current・finite control・boundedF2 を実際に exercise する。§15 の最初の pilot はその subset 全部の完了を名乗らない。

## 14. Adapter inventory / findings / research decision

| Interface | Status / required proof |
| --- | --- |
| #23 rich take/destroy source ending | **available / CLOSED**、single-root region claim bounds を保持。post-WFguardderivation と exact claim conservation を reuse |
| rich initialize / destination binding | **later FORMAL-SCOPE**、first subset の requirement ではない |
| raw primitive guard→localWF、physical/ledger frame | **new integration proof obligation**。existing legal post projection と別。flat initialize/end、fixed/rich updates、domainend の guard clauses を導く |
| capsule/frame ownership coherence | **new integration layer**。finite partition/local deps/disjoint footprints、loose carrier bijection、no owner duplication。既存 proof がこれを既に証明したとは言わない |
| ordinary flat call/return | **new scaffold**、actual body derivation、slotstart/end、caller-survivor guard、effect substitution。§15 で限定 pilot |
| finiteIf/Match/Return | **new control bridge**、all-arm checking→one-arm runtime、normal/Returnjoin 分離 |
| F2 body/header/exit adapter | **new bounded bridge**、§8 の flat restriction で rich fact erasure を不要にする。旧 body premise を global 安全性 oracle にしない |
| persistent ref/join、payload ref issuance | **FORMAL-SCOPE**。full formal interface は未実装だが first base から明示除外して依存しない |
| arbitrary nested/physical aggregate composition | **FORMAL-SCOPE**。fixed profile は semantic-only |
| F1.5 extension / B / C | optional/later 別 refinement。first F3.1 外 |

ここで「new integration proof obligation」はこの contract が設計する将来の checking/control/adapter lemma であり、canonical を補う仮定や既証明 interface を偽って置くものではない。利用可能な局所 kernel 上で具体的 rule/guard/frame として定義できる範囲に限定した。実装時にこれらが宣言した bounds で実証できない、あるいは canonical が operation に必要な前提を決められない場合は minimal witness を返し停止する。

**FORMAL-ENCODING:** capsule/profile metadata、symbolic state/ghost history、declarativechecking、adapternetwork は non-normative。**FORMAL-SCOPE:**上記 exclusions、rich preinitialized 限定、P7 complete join 非包含、flat loop+rich frame。**FORMAL-LEMMA:**guard-derived candidate WF、body/control/frame/loop lift が後続 proof obligations。**FORMAL-INTERFACE-GAP F3-IF-1:**#23 で bounded scope 解消済み、reverse legality は引き続き禁止。

今回の調査で新しい **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION** は見つかっていない。新たな blocking interface を oracle で埋めていない。外部 research は不要。property/architecture fork は existing project evidence、#23counterexample、bounded scope 裁定で解ける。M/P/R/newRedTeam を開始しない。

## 15. Exactly one bounded F3.1 handoff

**Recommendation: F3.1 — finite Seq/If + one ordinary direct-call scaffold + selected flat/rich lifetime adapters.** first Safe Core 全体ではなく、その non-vacuouscompositionpilot に限る。F3.0 で実装しない。

### Exact implementation bound

finite program に entry+ordinary callee 一つ、call-depth 一、monomorphic flat owned parameter 最大一、unit/Bool/flat loose package result、有限 Seq/If/Return。callee は再帰/call なし。loop/Match/fixed aggregate/domain finalize/relocation/fullrefjoin を pilot に入れない。

profile は Flat または Rich の tagged authority 一つで、instance ごとに一方を選ぶ。general 多 capsuleproduct を実装しない。Flat は一つの explicit region と有限 disjoint slot/root claims、caller/callee slot は各最大一。flat initialize/take/destroy/replace/store を扱う。Rich は#23 の one-root/region/claim、already-live、take/destroy と exact token local read/ending operand だけ。rich call は unit/Bool parameter と caller-owned root access operand、result は unit または loose returned value に限り、rich param/local/destination initialize なし。calls は actual same authority を保持し caller/callee ownership metadata だけを frame する。

Flat owned parameter は existing loose input を callee explicit slot へ initialize し、return take で caller loose carrier へ戻す。caller argument が installed なら明示 take を先に行う。callee scope exit は live owned locals を残さず、slot を caller claim frame へ返す。rich callee take result も loose carrier のまま返し、新 root への暗黙 initialize をしない。caller external dependency を callee guard から消さない。

### Files / imports

prospective additions:

| File | Responsibility |
| --- | --- |
| `NewLang/F3/Core/Model.lean` | finite typed AST、profile authority、explicit fault/outcome、frame/carrier representation |
| `NewLang/F3/Core/Operational.lean` | raw primitive attempt、Seq/If/Call/Return small-step、finite prefix。post-WF なし |
| `NewLang/F3/Core/Checking.lean` | declarative rules、symbolic exact dep/resource alternatives、actual callee-body derivation |
| `NewLang/F3/Core/Adapter.lean` | flat/rich raw guard→candidateWF、actual existing authority/claim/frame correspondence |
| `NewLang/F3/Core/Proofs.lean` | subject reduction、no-fault、finite prefix、call/selected branch/exit proofs |
| `NewLang/F3/Core/Counterexample/Scaffold.lean` | positive witnesses と isolated broken rules |
| `docs/F3_1_FINITE_CORE_SCAFFOLD_REPORT.ja.md` | evidence/clauses/audit/CI/claim limits |

reuse imports: `NewLang.F0.Replace`, `Store`, `Lifetime`, `Reference`, `WellFormed`; `NewLang.F1.Backing.Model`, `Lifetime`; `NewLang.F1.Occupancy.Model`, `Claims`, `Conversion`, `Lifetime`; `NewLang.F3.Memory.SumLifetime`, `Proofs`。既存 fixtures を reuse できるが production namespace に broken rule を混ぜない。Conditional fact/state は rich authority から参照し、erasure を rich legality proof に使わない。F2 等未接続 profile を import しただけで integration 完了と呼ばない。

### Theorems / controls / stop

planned theorem concepts:

- `checked_primitive_guards`、`checked_raw_candidate_preserves`：raw candidate と static exact guards から WF、claim frame、dependency validity を導く。
- `checked_selected_if_arm`、`return_is_not_normal`：全 arm 検査と一 arm 実行、normal/Return separation。
- `call_parameter_transfer_unique`、`call_return_preserves_dependency_data`、`callee_exit_no_local_dependency_escape`、`caller_survivors_remain_checked`。
- `scaffold_checked_step_preserves`、`scaffold_checked_attempt_no_fault`、`scaffold_finite_prefix_safe`：post-Safe 入力なしで actual AST/body finite execution を扱う。

required positive witnesses: 非空 flat owned call が parameter initialize→replace/store→take-return まで進む；If 両 arm checked で runtime one arm；Return-only arm と normal arm；rich 独立 take の loose return；rich old-only occurrence-dependent discardable value は atomic destroy で消費できる；same pre の rich self-dependent take は不合法だが destroy は合法。existing#23witness の名前変更だけでなく core execution/checking を接続する。

required negative controls: unchecked sibling arm、dupl/non-Copy parameter copy、wrong type/missing authority/wrong extent、lost/duplicated slot claim、non-Discardable discard、returned ended fact/occurrence、caller external old dependency 見落し、callee-local dependency escape、stale token、reverse coarse legality、Return を normal join へ混ぜる、raw candidate post WF を premise に追加した broken checker。少なくとも一つは raw execution 上の fault trace が存在する unchecked core を作り、normal checked counterpart では fault 排除されることを示す。

audit: existing 985 declarations を順序/whitelist ごと保持、全 new public checking/adapter/soundness/control declaration に`#print axioms`監査を追加。project-ownedLean に sorry/axiom/admit を残さない。pinned build/audit、dedicated branch、open/unmerged PR、exact-head PR-event Lean CI 必須。

**F3.1 stop:**この bounded scaffold の proof/witness/audit/CI を満たして review 待ち。full first Safe Core、F2 adapter、finite Match、fixed profile/general capsule composition、rich initialize、production/backend を同じ milestone へ拡大しない。later integration は別 Coordination handoff。F3.1 開始には F3.0 review 後の指示を要する。

## 16. Review handback / stop

今回は docs-only branch `f3.0-safe-core-contract`。baseline と最終 branch で`lake build` / `bash scripts/check-proofs.sh`を実行し 985 監査を維持する。PR exact head と pull_request-event `Lean proofs` run/job の result は [Issue #22 Track: F handback](https://github.com/wakairo/NewLang_FormalProof/issues/22) に記録する。Git/CI を正とし、本書に自己参照する commit SHA や独自 Version history を置かない。

F3.0-pre の CLOSED を維持し、契約の ready は global theorem 完了や Coordination approval を意味しない。PR と Issue を open のまま残し merge/close しない。canonical edit、Lean implementation、F3.1、M/P/R、新 RedTeam、rich initialize、callable/generic/Array-span、LLVM/FFI/modules/concurrency へ進まない。

**F3.0 CONTRACT READY FOR REVIEW**
