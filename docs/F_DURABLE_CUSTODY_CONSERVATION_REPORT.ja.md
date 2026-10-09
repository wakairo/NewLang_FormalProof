# Draft 17.29 — bounded durable LiveTail custody conservation

Track: F

Issue [#39](https://github.com/wakairo/NewLang_FormalProof/issues/39) の独立した有限 Lean adjunct。停止判定は **F DRAFT17.29 DURABLE CUSTODY CONSERVATION READY FOR COORDINATION REVIEW**。候補 PR は OPEN / unmerged とし、Coordination の review を待つ。これは compiler / native execution の証拠ではない。

## Authority と既存 evidence

- 開始時 Compiler main: `5e13a5009605389be1086b94896fc88994ca5d00`。
- 再開時確認 Compiler main: `b436c429d133704255c2fe6d0e022e3777d5af4f`。差分は production 側 PR #218 の source gate / 実装・test。`CURRENT_SPEC.md`、canonical Draft、Process / Design Procedure / Ledger に変更なし。この adjunct はその実装に依存しない。
- `docs/reference/CURRENT_SPEC.md` → `NewLang_v0_spec_Draft17_29.md`、特に §18.1c。§3.1–3.4、10–14、16、17.4、18.1a/b・18.6–8、26.4/7/11–13/17、27.3 の既存 responsibility / dependency / current-state rule と合わせて読む。
- FormalProof base main: `674c57a6a849ada370d0ebc7681fc4cf77937b54`。既存 #37 / PR #38 は producer の still-live RETURN の証拠であり、recipient 後の durable custody の証拠ではなかった。
- Compiler の `docs/NewLang_Project_Development_Process.md` と歴史的 design §4.2、Design Decision Procedure、Ledger DI-009–013 に従う。
- **Historical design audit: N/A — non-normative faithful finite model of adopted §18.1c.** 新しい language rule / design alternative を採用しない。canonical 内の candidate 表記を独自に修正しない。
- baseline `lake build` / `bash scripts/check-proofs.sh`: PASS、既存 **1306** declaration を保持。

## 有限モデルと前提・結論の分離

追加ファイル:

- `NewLang/Adjunct/Custody.lean`: 有限 state、guard、selected recipient body と各 candidate。
- `NewLang/Adjunct/CustodyProofs.lean`: symbolic applicability と preservation、拒否定理。
- `NewLang/Adjunct/Counterexample/Custody.lean`: producer からの concrete actual call、二つの failure world、refusal / positive / negative controls。

`KnownCall` の既存 **二つだけの heap root** と carrier table を再利用する。`heap` は #37 `LiveTail.State`、`approved` は既存 `KnownReturnAfterScope` による producer-return checkpoint。新しい caller-local sum C は heap backing でも user-visible LifetimeDomain でもなく、distinct `LocalRoot` / implicit `LocalLifetimeId` による lexical identity である。

`packet` は元の tail ptr/O/R/D と元の Allocation / Domain carrier を記述する **一つの metadata view**。`holders : Finset Holder` はその package が packet / formal / custody / displaced / saved / unpacked のどこにあるかを表す。複数 holder や空 holder を datatype で禁止していないため、duplicate / loss の不正 state は表現できる。`OwnerFrame.cover` が live tail に exactly-one holder を要求し、既存 carrier uniqueness / recorded binding invariant と `CarriesLiveH` correlation を組み合わせて preservation を証明する。released tail には holder が残らない。

元の Allocation identity は既存モデルと同じく **original region に対応する tail Allocation role** で表現する。transfer で変えるのは role を持つ ordinary binding ID と package placement ID であり、新しい Allocation / Domain / H を作らない。C root incarnation、heap O、package の ordinary placement、sum occurrence は別の identity。

元の #37 result envelope は carrier ownership を本 adjunct へ引き継いだ後 `consumed` / `bundle = none` に project する。この `consumed` は H_t の lifetime 終了ではない。`receiverView` は whole-unpacked packet を既存 terminal interface の stage に対応させる限定 adapter。精度を失う projection から逆向きに rich legality を推論しない。

### Source / control assumption

`Knowledge` は concrete tag とは別で、initializer / later replacement の **current ValueFact epoch** 付き exact-None source evidence、または Unknown / maySome。`KnowledgeSound` はその evidence と available / tag / current epoch の整合を要求する。これは source analyzer がどう evidence を生成するかの証明ではない。actual witness では initializer と唯一の later `replace(C,None)` からその stamp を構築する。body grammar / source AST / production inference /一般的 control join には拡張しない。

`DefinitionChecked` は有限 command list `replaceSome; consumeDisplacedNone; returnUnit` の certificate。`ConditionalDefinition` は有利な caller を固定せず、任意の symbolic sink / packet / state が明示的 applicability を満たす場合に preservation を導く。actual known call は別の theorem でその全条件を証明する。static `LiveTail` type、favorable sibling call、human CHECK は条件の代用にならない。

前提は pre-WellFormed、approved origin / exact current original owner、valid caller-local nonexclusive write-ref、current source-proved None、old-result slot が空である source-order guard、owner-value scope guard、fresh ghost IDs、surviving-dependency guard。**post-WellFormed、post-conservation、exactly-one post holder は applicability に含めない。** 全操作の post-WellFormed は定理の結論。

`ReadyPacket` は live original heap と Allocation / Domain **value** の借用 guard だけ。移転では root/domain/region ending authority、H の Discardable、platform release readiness を要求しない。terminal receiver は別途、既存 `RequiredAtEntry` と survivor / precise dependency guard を証明する。

## State transition と identity

| 段階 | package holder / current C | heap tail | C occurrence |
|---|---|---|---|
| approved producer return | caller packet / None | original O_t/R_t/A_t/D_t、live | absent |
| independent formal entry | callee formal | 同一、live | absent |
| recipient Some construction / replace / exact old-None consume | custody / Some(original) | 同一、live、release 0 | fresh P_C |
| recipient returns unit、first loan ends | custody / Some(original) | 同一、live | P_C live |
| fresh caller loan: replace C with None | displaced old Some / None | 同一、live | P_C ended |
| new loan ends、exhaustive old sum match | saved / None | 同一、live | absent、history retained |
| whole packet destructure | unpacked original fields | 同一、live | absent |
| independent terminal receiver | no owner / None | original tail released exactly once | absent |
| second exact-None consuming match | C value unavailable | tail remains released、head live | absent |
| independent head cleanup | no head/tail owner | both original roots released once | absent |

Formal entry is explicitly checked by `recipient_formal_entry_preserves_original_owner`; the atomic call candidate summarizes the same transfer into payload and records formal/frame IDs. `recipient_formal_bindings_consumed_on_unit_return` proves formal A/D do not remain available. Binding history, not reusable value data, retains those consumed IDs.

`LoanStep` は historically fresh scope ID を要求し、二つの caller loan の actual witness と、終了済み scope ID の再利用拒否を証明する。raw `openLoan` 単独の state preservation は scope permission を意味しない。

`usedFacts` / `usedOccurrences` は proof-only ghost history。freshness は既存 heap / producer history **と** C history の双方を調べる。root O_t と P_C を同じ ID に読み替えない。delayed extraction は P_C / payload fact を終了して履歴を残す。`OldSum` の value data に occurrence identity を含めず、packet の ptr/R/D/dependency data を保存するため、occurrence が payload と一緒に transfer / retarget する抜け道を作らない。

`extraDependencies` は既存 `LiveTail.Dependency` と F1 conditional `Fact` vocabulary を用いる bounded external-survivor overlay。LiveFacts は既存 heap facts と C current / occurrence / payload facts の和。別の sum 専用 dependency 種別は作らない。base package dependencies は既存 `LiveTail.WellFormed`、C overlay は `DependenciesValid` で確認し、`ChangeGuard` / `ScopeGuard` / `ExtraTerminalGuard` はそれぞれ終了する exact fact / scope を検査する。provenance を自動的に blocking occurrence dependency にしない。

## 二か所の consuming match と static capability

`optionCopyable` / `optionDiscardable` は **None と Some の両方で false**。runtime None に Drop を付与しない。

1. `recipientDisplaced`: sole adoption replace の old sum に adoption origin / source epoch 付き exact-None proof が必要。`recipient_old_result_has_exact_none_proof` が actual applicability から導く。old None の entire value を消費し、old owner payload は存在しない。
2. `callerFinal`: sole later replacement の `replacedNone currentFact`、C available / current None、新 loan 終了、displaced result 消費済み、terminal または refusal の source route が必要。

その間の `recoverPost` は None / Some の **exhaustive by-value match**。Some branch では packet を whole transfer、None branch では zero owner を消費する。`Some(_)`、old result の implicit drop、store、recipient の post-consume bool failure、arbitrary elsewhere の one-arm match は certificate を得ない。raw candidate function は guard を伴わない source permission ではない。

## Alias、scoped ref、Unknown、failure

sink は scope-bound ordinary write-ref。exclusive / noalias / lifetime-ending authority はない。`currentThrough` は同じ world / C に対する **metadata Current substitution** であり、expired ref の dereference permission ではない。read alias も caller-visible updated Some を見る。実際の操作は別の `SinkValid` を要求し、消えた loan は write を許可しない。alias list は substitution metadata、escape する semantic package の scope dependency は surviving-dependency overlay に載せる。

Unknown へ current knowledge を落としても concrete state の invariant は保たれるが、exact-None proof を復元できない。may-Some も同様。unknown heap owner identity の general abstract domain は今回実装せず、exact `CarriesLiveH` certificate がない場合に permission を与えない境界を保持する。

actual-call rejection は **pre-consume** に行い `checkedRecipient` はその場合 entire caller state を保存する。policy refusal は recipient 前の選択で元の packet / heap / C None を維持し、別途 whole destructure / terminal release に進む。移転後に false を返して original owner を隠す経路はない。これは runtime allocator rollback / exception recovery / production transaction の証明ではない。

allocation outcomes:

- 0: optional backing snapshot は cell / A / D を持たず、phantom release をしない。
- 1: head-only snapshot は explicit full extent / A_h / D_h で既存 end→slot→raw→finalize→deallocate の **各 primitive guard** を証明し、唯一の head を一度だけ解放する。
- 2: approved producer / adoption trace、または pre-consume refusal trace を machine-check。head/tail は独立。

0/1 control は `FailureSnapshot` の absent / present を区別する有限 branch evidence。既存 `KnownCall.State` は never-allocated root を表す phase を持たないため、absent root を「release済み」として global WellFormed に埋め込まない。head-only primitive signature の unused padding cell に KnownCall global invariant を主張しない。fallible allocator 自体や source branch coverage を証明したという主張ではない。

## Machine-checked inventory

以下は `NewLang.Adjunct.Custody`（concrete は `.Counterexample`）の主要定理。新しい **全93 public theorem** を audit に登録した。

| obligation | symbolic / concrete evidence |
|---|---|
| independently conditional definition / actual call | `recipient_definition_is_conditional`, `actual_recipient_call` |
| preからpost invariant を導出 | `recipient_preserves_wellFormed`, `extraction_preserves_wellFormed`, `recovery_preserves_wellFormed`, `unpacking_preserves_wellFormed`, `terminal_preserves_wellFormed`, `final_exact_none_consumption_preserves_wellFormed` |
| original heap /責任保存 | `recipient_preserves_original_heap`, `recipient_preserves_responsibility`, `recipient_returns_unit_with_live_tail_in_caller_custody` |
| donor / formal 消費 | `recipient_consumes_original_donor_bindings`, `recipient_formal_bindings_consumed_on_unit_return` |
| fresh conditional identity /歴史 | `recipient_creates_only_a_conditional_occurrence`, `recipient_fresh_in_combined_occurrence_history` |
| occurrence非transfer | `extraction_does_not_transfer_occurrence`, `original_packet_extracted_without_occurrence_transfer` |
| exactly-one / no loss | `recipient_transfers_exactly_one_owner`, `noncopy_holder_cannot_duplicate`, `live_noncopy_owner_cannot_be_forgotten` |
| current aliases / expired permission | `aliases_observe_the_same_caller_post`, `nonexclusive_alias_gets_current_post`, `ended_loan_never_grants_write_permission` |
| two exact-None sites | `recipient_old_result_has_exact_none_proof`, `actual_second_exact_none_site`, `recipient_old_none_consumed_without_discardability` |
| independent terminal / head | `actual_independent_terminal_receiver`, `terminal_releases_original_tail_once_keeps_head`, `head_cleanup_has_its_own_primitive_guards` |
| complete positive trace / no double free | `complete_adopt_extract_release_trace`, `two_original_roots_released_once_after_durable_custody`, `original_tail_not_double_freed` |
| refusal / 0 / 1 allocation worlds | `refusal_before_consume_preserves_owner_then_releases`, `refusal_independent_head_cleanup_releases_both_once`, `zero_allocation_failure_has_no_owner_or_release`, `one_allocation_failure_has_guarded_exact_head_cleanup` |

## Specific negative / break controls

| 攻撃 | reject / falsifier |
|---|---|
| sink already Some | `already_some_sink_rejected` |
| Unknown / may-Some を None とみなす | `unknown_sink_rejected_without_optimistic_none`, `may_some_cannot_mint_zero_owner_proof` |
| old / final None の source証拠なし | `erased_source_knowledge_cannot_supply_displaced_none_match`, `final_none_consumption_needs_its_source_replacement` |
| general one-arm None / runtime Drop / wildcard / bool failure | `arbitrary_one_arm_none_is_not_admitted`, `runtime_none_does_not_enable_store_drop_or_bool_failure` |
| foreign world / wrong original O/R/D | `foreign_sink_world_rejected`, `nominal_packet_cannot_certify_wrong_original_incarnation`, `...region`, `...domain` |
| copied ptr without Allocation | `copied_ptr_cannot_replace_missing_allocation_owner` |
| read-only / expired / noncaller sink | `readonly_sink_rejected`, `expired_sink_ref_rejected`, `non_caller_owned_sink_rejected`, `stale_recipient_loan_cannot_write_caller_after_return` |
| historical P reuse | `reused_occurrence_rejected` |
| live borrowed sink scope escape | `live_sink_scope_cannot_escape_recipient`（pre-state は WF） |
| surviving P_C dependency | `occurrence_observer_blocks_delayed_extract`（pre-state は WF） |
| dependency guardを外す | `unchecked_extract_keeps_heap_but_breaks_dependency`：original heap / owner移転は残るが、ended P_C dependency が不正 |
| holder duplication / forgetting | `duplicate_owner_holder_breaks_invariant`, `forgotten_owner_holder_breaks_invariant` |
| post-consume failure hides owner | `after_consume_failure_cannot_hide_custody` |
| saved reuse / double release | `saved_packet_cannot_be_reused_after_unpack`, `terminal_cannot_release_twice` |
| transferをterminal permissionと混同 | `live_tail_dependency_survives_recipient_but_blocks_terminal`, `recipient_requires_no_heap_lifetime_ending_authority` |

## FORMAL findings / 未モデル化の境界

- **FORMAL-ENCODING**: caller C の implicit local lifetime と heap O/R/D、ordinary binding placement、conditional P_C を分離。holder support は existing carrier table の view。ghost history / route / epoch evidence は runtime layout・counter 要件ではない。**Formal representation choices are non-normative.**
- **FORMAL-LEMMA**: carrier uniqueness + historical fresh binding + pre owner correlation から donor/formal消費と exactly-one post owner を導出。C occurrence を消しても original heap identity / responsibility は変わらない。post invariant を前提にしない。
- **FORMAL-LEMMA**: root-ending blocker / live tail observation があっても custody transfer は可能。terminal の別 applicability は終了する facts / authority を独立に確認し、必要なら拒否する。
- **FORMAL-ENCODING**: 0/1 allocation failure は optional snapshot。never-allocated と already-released を混同せず、存在する head に対する primitive disposal guard を証明する。
- **FORMAL-SCOPE**: parser / checker が source-proved None、closed selected body、conditional contract、alias substitution、Current effects を生成する refinement は未証明。root / region / domain が Unknown な一般 abstract domain、general effect / borrow system はない。
- **FORMAL-SCOPE**: native allocator、physical bytes / ABI、runtime behavior、production artifact、exceptions / allocator rollback、一般 owner graph、一般 Option theorem、5-root cJSON、F3.1全体、他Trackを証明しない。P #217 / PR #218 に proof dependency はない。
- **FORMAL-HOLE / FORMAL-AMBIGUITY**: この closed finite profile で新しい blocker は見つからなかった。canonical を補完・変更していない。上記 source-to-model / runtime境界は未証明であり、soundness claim を越えて扱わない。

## Verification とreview receipt

- Lean / Lake `4.34.1`、elan `4.2.4`、`lean-toolchain` は変更なし。
- mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`、manifest / bootstrap / workflow は変更なし。
- `lake build`: PASS（789 jobs）。`bash scripts/check-proofs.sh`: PASS。
- baseline1306 + new93 = **1399** declarations。project-owned `sorry` / `axiom` / `admit` を禁止し、許可する proof dependency は既存どおり `propext` / `Classical.choice` / `Quot.sound` のみ。
- 固定 candidate head、local結果、pull-request-triggered `Lean proofs` run / job結果は PR と Issue #39 の Track F handoff に記録する。document に別の Version history は設けず、変更履歴は Git を正とする。
- PR は OPEN / unmerged。Coordination review 待ちで停止し、後続taskを開始しない。
