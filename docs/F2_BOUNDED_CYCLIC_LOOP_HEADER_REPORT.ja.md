# F2 — bounded cyclic loop-header formal kernel

[English companion](F2_BOUNDED_CYCLIC_LOOP_HEADER_REPORT.md)

FormalProof [Issue #19](https://github.com/wakairo/NewLang_FormalProof/issues/19)のF2だけを実装します。最初にCompilerのdevelopment processを読み、両repositoryのcurrent mainを確認しました。

| Authority / baseline | 確認した値 |
| --- | --- |
| Compiler main | `2a3643449ae5d9fa619909c9fa16d21b8d2ac5e6` |
| CURRENT_SPEC | **Draft 17.16** |
| 正本 | [Compiler Draft 17.16](https://github.com/wakairo/NewLang_Compiler/blob/2a3643449ae5d9fa619909c9fa16d21b8d2ac5e6/docs/reference/NewLang_v0_spec_Draft17_16.md) |
| FormalProof base main | `a3a8c70becb3da6a9c2fc6f91ca578f49b19df32` |
| 専用branch | `f2-bounded-cyclic-loop-header` |
| baseline build / audit | PASS / **834** declarations |

Draft 17.4はhistorical snapshotのまま保持します。F0/F1のLean fileと既存public statementは変更しません。Gitを変更履歴の正とし、独自Version historyは持ちません。

## State/modelと既存kernelとの境界

`ConcreteHeaderState`はlanguage stateのbounded sliceであり、Unknownを含みません。non-Copy parameterを0または1個、captured outer non-Copy availabilityを1個、outer Copy/current-value componentを1個持ちます。`Signature`がslot/typeとentry availabilityを固定し、parameter countはoptional slotから導出します。`HeaderWellFormed`はstatic type、exact affine carrier、history、exact availability、iteration-scope終了、surviving dependency livenessを検査します。outer mutable placeの旧factを安定external factへ混ぜて永続化しないよう、`externalSeparation`でそのplaceを`publicFacts`から除外し、current-value factは別のliveness分岐で扱います。

`AbstractHeaderState`だけがproof情報 **H** を持ちます。origin / hidden dependency / current factにfinite may-setまたはUnknownを使い、`Represents`がexact layerとmay inclusionを結びます。Unknownは全alternativeを包含し、空集合ではありません。symbolic originは無限に異なるconcrete packageを表せますが、各concrete stateのaffine責任は常に一つです。availabilityにMaybe/wideningを導入しません。`Widen`はsignatureと全may-alternativeを保存し、blockerを消せません。correlationを失うと精度は下がり得ますが、安全判定を強くしてはいけません。

F0の`PackageId`、`PlaceId`、`ValueFactId`、`Fact`を再利用します。F2の`Package`はidentity/static type/dependencyだけのviewで、既存F0/F1のValuePackageを置き換えません。`BindingId`はpackage/incarnationとは別です。`Dependency.externalFact`は既存factのwrapper、`.iteration`は今回終了するiterationへのblocking依存です。persistent ptr provenanceを自動的にblocking dependencyへ変換しません。

`usedBindings` / `usedPackages` / `usedFacts`はproof-only ghost stateです。具体witnessのmax-plus fresh supplyもruntime/compiler counter要件ではありません。**Formal representation choices are non-normative.**

`Loop.edges`はstatic reachabilityとして供給されたfinite edge familyです。continue/break/returnそれぞれ最大2 indexのbounded sliceです。`Loop.body`はordinary semantic transferの明示premiseであり、expression評価、Copy assignment、resource消費/生成、acyclic call、function returnの未model化義務はbody/caller checkerに残します。任意のdestructionを許可する定理ではありません。F1.5のmemory/relocation全体をloop theoremへ押し込まず、full erasureやwhole-language safetyを主張しません。

## Continueとinductive post-fixpoint

`Continue`はsupplied continue edge、body relation、well-formed両endpoint、`ContinueFrame`から成ります。fresh iteration bindingへunchanged Pまたはtransformed fresh same-type Qを渡します。carrierはpostのbinding/package pair一つで、old責任は残りません。static type equalityはpackage identity equalityを意味しません。historyはmonotonicで、Copy current-value変更時にはhistorically fresh factを記録します。旧current factはnon-liveです。unchanged affine packageに旧factへのhidden dependencyが残ればcandidateはrejectされます。

`PostFixpoint`はentry inclusionと**供給された全continue edge**へのclosureです。`Trace`は任意の有限edge列、`Reachable`はentry/backedgeのinductive closureです。有限traceとreachabilityの対応、全有限列に対するrepresentation soundnessを証明します。termination、least fixpoint、runtime package IDの有限列挙、production widening algorithmを要求しません。

2-edge witnessでは、任意の`List (Fin 2)`についてlegal traceが実際に存在し、終点を同じHで包含します。edgeごとにhidden dependency、origin、current factが変わります。unchanged carryではexternal hidden dependencyが任意のtraceで再帰します。transformed carryはold Pを消費しfresh Qを唯一の責任として持ちます。pure Copy witnessはaffine slotなしでouter Copy current factを更新するcounter-like stateであり、数値counter payloadまではmodel化しません。

さらに、reachable集合の外にあるvalid extra stateを包含する、より大きいinductive Hを具体的に証明します。leastでなくてもsoundですが、first-entry-onlyやedge省略のunder-approximationはsoundではありません。

## Finite break exit / return / zero-break

headerへ戻るのはcontinueだけです。`breakEdges`はfinite **static index set**であり、runtime result PackageIdの有限列挙ではありません。`IndexedBreakBound`は確立済みHから各break edgeをsummaryへ解析し、`FiniteBreakJoin`は全summaryのtype / Copy capability / captured availabilityを揃え、origin/dependency/current-fact alternativeを包含します。`finite_break_join_sound`が全normal resultへのsoundnessを証明します。

具体exitはheader historyからfreshなpackage/current-fact IDを選び、finite edge summaryはそれらのunbounded runtime identityをUnknownで包含します。後続iterationが再利用し得る固定result IDを予約しません。Copy/non-Copy exit sliceには異なるstatic TypeIdを使います。Copy結果のjoin、同型で異なるnon-Copy PackageIdのbreak結果を許可します。non-Copy concrete resultのcarrierは一つです。break後availabilityはentryと異なってよく、break間では一致させます。`ExitFactsLive`とscope guardでsurviving blockerを保持します。exit current-fact観測のordinary生成/transferはbody境界にあり、header allocation history theoremをfunction exit全体へ拡張しません。

returnはfunction-exit pathであり、header recurrenceにもbreak-result setにも入りません。continue/returnが存在してもbreak edgeが0ならnormal resultは0です。Unit/bottom/neverを捏造しません。runtime値を理由にsupplied static edgeを削除するconstant propagationは実装しません。

## Required positive witnesses

| Issue #19 | machine-checked evidence | 正本clause |
| --- | --- | --- |
| 1 pure Copy cyclic state | `pure_copy_cyclic_sound`, `every_finite_edge_sequence_is_sound false` | §13.5a, §27.5–6/11 |
| 2 unchanged non-Copy | `unchanged_symbolic_affine_carry`, `unchanged_postFixpoint`, `hidden_dependency_recurs_without_erasure` | §27.5–6 |
| 3 transformed non-Copy | `transformed_affine_carry`, `Continue.transformed_transfer_exactly_once` | §27.5–6 |
| 4 two edge alternatives | `two_edges_distinct_alternatives`, `cyclic_postFixpoint`, `every_finite_edge_sequence_has_trace` | §13.5a, §27.5–6/11 |
| 5 exact outer availability | `all_continue_sequences_exact_availability`, `Continue.outer_availability_exact` | §27.5–6 |
| 6 finite break alternatives | `finite_copy_break_alternatives`, `finite_noncopy_break_alternatives`, `finite_exit_analysis_after_inductive_header` | §27.7–8/11 |
| 7 zero break | `zero_break_postFixpoint`, `zero_break_still_has_continue`, `zero_break_cannot_synthesize_unit_like_result` | §27.9 |
| 8 larger sound H | `larger_header_is_inductive`, `larger_than_reachable_is_still_sound` | §27.6/11 |

## Required negative controls

unrelated invariantを保てる箇所では、type/scope/carrier等を併記し、壊した義務を分離しました。production relationを弱めるbroken ruleは追加しません。

| Issue #19 | control | 破る義務 / 正本clause |
| --- | --- | --- |
| 1 first-entry-only H after Copy mutation | `first_entry_only_is_not_inductive` | current-fact包含/全backedgeclosure、§13.5a, §27.6/11 |
| 2 same type implies same package | `same_type_does_not_mean_same_package` | package identity、§27.5–6 |
| 3 transformed retains old+new | `duplicated_affine_responsibility_rejected` | exact carrier、§27.5–6 |
| 4 loses both responsibilities | `lost_affine_responsibility_rejected` | slot responsibility、§27.5–6 |
| 5 outer availability changes on continue | `outer_availability_cannot_be_widened` | exact entry/backedge availability、§27.5–6 |
| 6 iteration-local dependency crosses continue | `iteration_local_dependency_cannot_escape` | scope終了、§27.5–6 |
| 7 join drops blocker | `dropped_join_blocker_looks_safe_but_conflicts` | sound dependency inclusion、§13.5a, §27.6/11 |
| 8 omits one of two edges | `omitted_continue_edge_breaks_closure` | 全backedgeclosure、§27.6 |
| 9 break feeds header | `break_does_not_feed_header` | control-flow separation、§27.7 |
| 10 return feeds header | `return_does_not_feed_header` | function exit separation、§27.7/9 |
| 11 return in break-result set | `return_is_not_a_break_result` | break-result coverage、§27.7–9 |
| 12 zero break synthesizes unit | `zero_break_cannot_synthesize_unit_like_result` | zero normal exit、§27.9 |
| 13 Unknown means dependency-free | `unknown_retains_concrete_blocker` | Unknownのover-approximation、§27.11 |
| 14 changing/fork origins collapsed by type | `fork_identity_cannot_collapse_to_type`, `origin_singleton_loses_fork_alternative` | package alternatives、§27.5–6/8 |
| 15 under-approximate H claimed sound | `underapproximation_is_not_sound` | reachable state coverage、§27.6/11 |

追加control `copy_mutation_does_not_clear_hidden_affine_blocker`はwell-formed preとunchanged packageを保ったままCopy factを更新し、旧fact依存のsurvivorがrejectされることを示します（§13.5a, §27.6/11）。

## FORMAL findings / scope exclusions

- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION: 新規なし。** 参照したcanonical ruleを強化・修正してproofを成立させていません。
- **FORMAL-ENCODING:** bounded orthogonal control-flow state、既存nominal fact/package、exact layerとmay/Unknownの分離、ghost freshness、finite static edgeごとのexit summary。F1.5全体へのerasureは主張しません。
- **FORMAL-LEMMA:** entry + all continue closureから任意finite sequenceを包含し、exact affine / availability / scopeを保持します。wideningはblockerを消さず、finite break analysisはH確立後に行います。
- **FORMAL-SCOPE:** one-loop bounded kernelだけです。nested loopは同kernelのnested instanceとして扱う方向ですがcomposition theoremは未証明です。acyclic body-sensitive callはtransfer premise、recursive function SCCはscope外です。exact source grammar、frontend/source checker、production implementation、M/P/R、memory/relocation変更、LLVM、FFI、modules、concurrencyへ進みません。

## Build / audit / CI / handoff

Lean/Lake **4.34.1**、elan **4.2.4**、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、manifest、bootstrap、workflowは不変です。baseline **834**件を順序どおり保持し、以下のpublic **96**件を追加して**930** auditです。private fixture helper 2件はaudited public proofの依存に含まれます。project-owned Leanに`sorry` / `axiom` / `admit`はなく、許可logic dependencyは`propext` / `Classical.choice` / `Quot.sound`だけです。

検証は`lake clean newlang-formal`、`lake build`、`bash scripts/check-proofs.sh`。exact commit / open PR / **pull_requestイベントのLean proofs CI結果**はlocal検証とCI完了後、[Issue #19](https://github.com/wakairo/NewLang_FormalProof/issues/19)の最終**Track: F** handoffへ記録します。report自身のcommit SHAを埋めて循環させません。PRもIssueもopenのまま、merge/closeせず**F2 READY FOR REVIEW**で停止し、Coordination review / Semantic Syncへ返します。

## Exact audited theorem inventory / Draft 17.16 mapping

以下は追加auditと完全一致します。qualified nameのprefixは表に明示し、各declarationを定義するfileとcanonical clauseを対応させます。count/type/slotの構造的境界は§27.2–3/§27.5、scope/affine proofは§27.5–6、cyclic over-approximationとdependencyは§13.5a/§27.6/§27.11、exitは§27.7–9です。

### NewLang/F2/Abstract.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.May.join_left` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.May.join_right` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.May.unknown_contains` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.represents_widen` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.represented_safety` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.widening_never_erases_blocker` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.lost_correlation_cannot_justify_invalidation` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.unknown_is_not_dependency_free` | §13.5a; §27.5–6, §27.11 |

### NewLang/F2/Counterexample/Affine.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.Counterexample.same_type_does_not_mean_same_package` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.duplicated_affine_responsibility_rejected` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.lost_affine_responsibility_rejected` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.outer_availability_cannot_be_widened` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.iteration_local_dependency_cannot_escape` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.fork_identity_cannot_collapse_to_type` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.origin_singleton_loses_fork_alternative` | §13.5a; §27.5–6 |
| `NewLang.F2.Counterexample.copy_mutation_does_not_clear_hidden_affine_blocker` | §13.5a; §27.5–6 |

### NewLang/F2/Counterexample/Cyclic.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.Counterexample.pure_copy_cyclic_sound` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unchanged_continue` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unchanged_postFixpoint` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unchanged_symbolic_affine_carry` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.hidden_dependency_recurs_without_erasure` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.transformed_affine_carry` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.two_edges_distinct_alternatives` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.all_continue_sequences_exact_availability` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.first_entry_only_is_not_inductive` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.underapproximation_is_not_sound` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.omitted_continue_edge_breaks_closure` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.larger_header_is_inductive` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.larger_than_reachable_is_still_sound` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.dropped_join_blocker_looks_safe_but_conflicts` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unknown_retains_concrete_blocker` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.every_finite_edge_sequence_has_trace` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.every_finite_edge_sequence_is_sound` | §13.5a; §27.5–6, §27.11 |

### NewLang/F2/Counterexample/Exits.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.Counterexample.exit_wellFormed` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.exit_dependencies_live` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.exits_postFixpoint` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.exit_represented` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_break_bound` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.concrete_break` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_copy_break_alternatives` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_noncopy_break_alternatives` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.break_does_not_feed_header` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.zero_break_edge_set` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.zero_break_postFixpoint` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.zero_break_still_has_continue` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.concrete_return` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.return_does_not_feed_header` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.return_is_not_a_break_result` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.zero_break_cannot_synthesize_unit_like_result` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_indexed_break_bound` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_indexed_join` | §27.7–9, §27.11 |
| `NewLang.F2.Counterexample.finite_exit_analysis_after_inductive_header` | §27.7–9, §27.11 |

### NewLang/F2/Counterexample/Fixture.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.Counterexample.next_binding_unused` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.next_package_unused` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.next_fact_unused` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.entry_wellFormed` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.advance_dependencies` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.advance_wellFormed` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.advance_frame` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unchanged_wellFormed` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.unchanged_frame` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.entry_represented` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.advanced_represented` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.cyclic_continue` | §13.5a; §27.5–6, §27.11 |
| `NewLang.F2.Counterexample.cyclic_postFixpoint` | §13.5a; §27.5–6, §27.11 |

### NewLang/F2/Exit.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.break_edges_finite` | §27.7–9, §27.11 |
| `NewLang.F2.break_is_normal_exit` | §27.7–9, §27.11 |
| `NewLang.F2.continue_excludes_break_return` | §27.7–9, §27.11 |
| `NewLang.F2.break_excludes_header` | §27.7–9, §27.11 |
| `NewLang.F2.return_excludes_header_and_break` | §27.7–9, §27.11 |
| `NewLang.F2.zero_break_has_no_normal_result` | §27.7–9, §27.11 |
| `NewLang.F2.reachable_break_summary_sound` | §27.7–9, §27.11 |
| `NewLang.F2.break_types_availability_agree` | §27.7–9, §27.11 |
| `NewLang.F2.break_runtime_affine_unique` | §27.7–9, §27.11 |
| `NewLang.F2.exit_representation_monotone` | §27.7–9, §27.11 |
| `NewLang.F2.finite_break_join_sound` | §27.7–9, §27.11 |

### NewLang/F2/Reachability.lean

| Qualified declaration | Draft 17.16 |
| --- | --- |
| `NewLang.F2.entry_reachable` | §27.5–6, §27.11 |
| `NewLang.F2.continue_preserves_reachability` | §27.5–6, §27.11 |
| `NewLang.F2.trace_preserves_representation` | §27.5–6, §27.11 |
| `NewLang.F2.arbitrary_finite_continue_sound` | §27.5–6, §27.11 |
| `NewLang.F2.post_fixpoint_sound` | §27.5–6, §27.11 |
| `NewLang.F2.trace_implies_reachable` | §27.5–6, §27.11 |
| `NewLang.F2.trace_append_step` | §27.5–6, §27.11 |
| `NewLang.F2.reachable_has_finite_trace` | §27.5–6, §27.11 |
| `NewLang.F2.any_inductive_overapproximation_suffices` | §27.5–6, §27.11 |
| `NewLang.F2.header_count_and_slot_correspondence` | §27.2–3, §27.5–6 |
| `NewLang.F2.represented_exact_layer` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.next_binding_fresh` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.outer_availability_exact` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.no_iteration_dependency_escape` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.affine_slot_unique` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.unchanged_transfer_exactly_once` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.transformed_identity_distinct` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.transformed_transfer_exactly_once` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.histories_monotone` | §27.5–6, §27.11 |
| `NewLang.F2.Continue.mutated_current_fact_is_not_live` | §27.5–6, §27.11 |
