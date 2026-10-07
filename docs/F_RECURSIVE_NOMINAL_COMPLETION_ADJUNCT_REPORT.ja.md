Track: F

# Bounded recursive nominal header / exact completion adjunct

## Authority と scope

[FormalProof Issue #33](https://github.com/wakairo/NewLang_FormalProof/issues/33) の F-A〜F-G だけを対象とする。
作業開始時に Compiler main の [開発運用方針](https://github.com/wakairo/NewLang_Compiler/blob/46e07d7f627fc037dc794c3edb28d720815ca196/docs/NewLang_Project_Development_Process.md) と `CURRENT_SPEC.md` を確認した。

| Authority | Exact source |
| --- | --- |
| Compiler main | `46e07d7f627fc037dc794c3edb28d720815ca196` |
| Canonical | [Draft 17.21](https://github.com/wakairo/NewLang_Compiler/blob/46e07d7f627fc037dc794c3edb28d720815ca196/docs/reference/NewLang_v0_spec_Draft17_21.md) §16.3、§4.4–5、§10、§26.2、§28.3 |
| FormalProof base main | `1d74649a848c8c1938dd8342383573464c676f94` |
| Branch | `f-recursive-nominal-completion` |

GitHub API の current main は Issue authority と一致した。Git transport の `main` ref は古い値を返したため、上記 FormalProof SHA を直接 fetch / checkout して baseline を検証した。古い ref の build を authority evidence に使わない。production implementation の representation / branch は proof input に使わない。

Canonical §16.3 は semantic unit あたり at most one の exact recursive aggregate shapeを admit する。本 model の完成可能な fields は、distinct field identities、declaration order の link `Option<ptr<H>>` と payload `u8` だけ。direct by-value cycle 等の型表現は攻撃入力であり、source admission の拡大ではない。

**Formal representation choices are non-normative.** Nat wrapper、finite record、List / Finset、graph rank、proof depth、classical decisionは proof encoding。C layout、ABI、source byte offset、runtime type tag、compiler registry implementation を要求しない。

## F-A — state / type-graph boundary

`NewLang/Declaration/Completion.lean` は次の小さい独立 layer を追加する。

- nominal `NominalId` と `FieldId`。runtime `IncarnationId` / `PlaceId` / provenance と型を分ける。
- `Header` は stable nominal identity、二つの field labels、`incomplete` / `complete fields` phase。
- `Fields` は declaration-order の二 field identity/type。source name admission / label resolution を通過した semantic input を受け取る。parser、name allocator、full symbol table は実装しない。
- finite `Ty` expression は byte、nominal identity、direct nominal ptr target、ordinary Option payload、unresolved attack marker。arbitrary generic、ref / slot recursion barrier、type binder、alias unfolding は追加しない。
- `ValueEdge` は aggregate field と Option payload edge。`TargetEdge` は ptr の typed nominal target relation。二 relation を混ぜない。
- candidate graph は proposed fields を検査する。未commitな fields を public completed declaration と扱わない。

`Eligible` は incomplete phase、same requested nominal identity、distinct labels、exact field identity binding、exact selected types、`NoValueCycle` を要求する。`CompleteStep` は eligibility と exact candidate equation。post invariantをoracleとして受け取らず、identity/fields/types をこの transition から導く。`complete?` と relation の対応も証明する。これは classical な proof-level decision functionであり、production cycle algorithm / termination complexity の実装ではない。

## F-B — nominal identity と runtime の分離

completion は Header の phase だけを更新する。nominal identity と declaration-order labels は不変で、他 declaration の identity を request に代入すると reject。incomplete phase は complete phase と同時に成立しない。

`World` は declaration state と既存 `F0.State` を分ける。`PtrFormation` は known header の direct target に対する pure type operationで、post world は pre world と同一。`CompletionInWorld` は declaration-only completion と runtime equality の積。runtime occupancy、used incarnation history、package tableの不変を証明し、empty runtime で positive witness を与える。type expression `.ptr H` は `F0.PtrToken` value ではない。

この claim は bounded model が runtime state/value を生成しないというもの。production compiler の safe ptr issuance、object lifetime-start、provenance derivation、foreign constructionを証明しない。数学的 record constructor の存在は source-level value construction permission ではない。

## F-C — recursion barrier と finite graph evidence

value-containment cycle は `Relation.TransGen ValueEdge` で H 自身へ戻る nonempty path。direct field `H` と Option payload `H` には具体的 cycleがあり、completion は rejectされる。ptrには outgoing `ValueEdge` がなく、ptrから始まる任意nonempty containment pathは不可能。

selected shape は次の経路を持つ。

```text
H --field--> Option<ptr<H>> --payload--> ptr<H>
                                             |
                                      typed target relation
                                             |
                                             H
```

最後の typed target relation は containment ではない。finite expression rankを使い、selected candidate の全 value edge が strict decreaseすることから cycle不在を導出する。rankは type-graph proof measureで、runtime size / field offsetではない。

broken graph control は `ValueEdge ∨ TargetEdge` を traversalに入れる。その誤った graph には selected Node の cycleができるが、正しい candidate は acyclic。missing ptr barrier の `Option<H>` は逆に本当の value cycleとなる。

exact source shapeでは `ExactTypes` から acyclicityを証明できるので、`NoValueCycle` guard は論理的には redundant。従って「この exact profile で cycle guardだけを消せば by-value cycleをadmitする」とは主張しない。cycle criterion自体と、profileに入らない cycle attacksを別々に検証している。future field admissionを広げる場合は、この criterionの検証を再利用/拡張する必要がある。mutual declaration sourceは今回 admitしない。

## F-D — Option / property composition

`Derives header capability depth type` は finite proof tree。ptrとbyteはdepth 0、ordinary Optionはpayload derivationのdepth+1、nominal aggregateは両field derivationのmax+1。

- ptr ruleには target H の completion / property premiseがない。
- Option ruleは任意payloadの同じcapabilityをcomposeし、optional pointer専用ruleはない。
- nominal ruleは exact `CompleteStep` certificate、committed field data、各field propertyのproofを要求する。
- incomplete H の nominal property query は reject。手で complete phaseを書いたことだけをnominal propertyの証拠としない。
- selected completion後、Copy(H) / Discardable(H)は両方とも**depth 2**で導出できる。H自身のpropertyを再帰的に問い合わせるfixed pointは必要ない。
- repeated `Option<ptr<H>>` のtype identityはconstructorとsame target nominal identityから決まる。source parsing / name resolutionのcorrectnessはこのequality theoremのscope外。

一般 theorem `nominal_property_requires_exact_completion` は nominal property proofからexact completion certificateと両fieldのpropertyを取り出す。unknown targetのptr property自体がconstructorから導けても、そのtargetのsafe type formationを許可することにはならないというcontrolもある。

## F-E — exact completion / failure abstraction

completionはonceだけ。complete phaseからはsame fields / inconsistent different fieldsのどちらでも次のcompletionが成立しない。

`stage` は private requestsを処理する。最初のcompletionが成功した後のduplicate requestでも、全stageのresultはnoneとなる。`registrationResult` は initial incomplete header、successful stage、completed final fieldsが揃ったときだけaccepted artifactを返す。incomplete final、unresolved field、empty request sequence、already-complete initial stateはrejectする。

登録成功について次を証明した。

1. initial headerはincomplete。
2. request列はexactly一件で、その`CompleteStep`が存在する。
3. final phaseはcompleteで、public artifactはそのexact fields / identity / labelsを持つ。
4. public artifactのtypeはexact `Option<ptr<H>>` / byte。

`publish` はopaqueなprior public snapshotを受け取り、whole registrationがacceptedの時だけcompleted artifactを公開する。failureではsnapshotをそのまま保持する。private stageが一度成功した後で失敗してもpartial completionを公開しないというconcrete witnessがある。

これは **abstract atomic commit boundary** の証明。実際のcompilerのmutation rollback、cache invalidation、error recovery、namespace collision handling、既存registry全体のWFは証明しない。old snapshotはopaqueな既存contextであり、その内部の正当性をこのtaskで推論しない。failure kindsはrejectedにまとめ、診断の優先順位を規定しない。

## F-F — bounded collection / ordering

`Event` はこのclosed categoryのsemantic Plan、またはopaque other/body-position tag。Planはsource offset由来ではないstable identityをすでに持つ。collectionは `headerSet` と `headerCount` に分ける。

- 任意simple physical permutationでheader membership/setが同一。
- declaration occurrence countも同一なので、at most one admissionは順序に依存しない。
- set/countを入力に取る任意deterministic consumerの結果も同一。
- concrete Planをbody tagの前後へ移しても同じsuccessful completion result。
- duplicate identical PlanをFinsetだけでcollectするとsingletonに潰れるが、countは2を保持してbounded admissionをrejectする。

これはbounded semantic collectionの結果。source textからのstable ID assignment、all future declaration categoriesのforward visibility、module registry、body checking implementationのorder independenceではない。full source-order theoremを得たと拡大解釈しない。今回要求されたbounded collection theoremにFORMAL-ENCODING gapは残らない。

## F-G — concrete controls と traceability

`NewLang/Declaration/Counterexample/Completion.lean` に25 controlsを分離し、production layerにbroken graph ruleを入れない。fixtureのNominalId/FieldIdはopaque semantic IDsで、Node/next/payloadをbuiltin nameにしない。

| Canonical / task | general evidence / concrete controls |
| --- | --- |
| §16.3.1 / F-B | identityとlabels保存、identity substitution拒否、incomplete/completeの排他 |
| §16.3.2 / §10 / F-B/D | incompleteでptr/Option property合法、H property拒否、unknown target formation拒否、empty runtime不変 |
| §16.3.3 / §26.2 / F-D | ordinary Option compositionとexact type identity、completion後のfinite Copy/Discardable |
| §16.3.4 / F-C | direct by-value cycle / Option-without-ptr cycle拒否、typed targetをcontainmentに混ぜるfalse-cycle control |
| §16.3.5 / F-E | legal completion/registration witness、same/different二回目拒否、field identity/order/duplicate-label/ptr-target substitution拒否、unresolved/empty/forged phase拒否 |
| §16.3.5 transaction / F-E | staged first success + failed second completionでpublic snapshot不変。exact completion / field set / one-requestのsuccess certificate |
| §16.3.6 / §28 / F-F | physical permutation、before/after body tag、duplicate-preserving occurrence countとset-only break test |

pointer-only linkはptr barrier criterionには合うが、今回のexact closed `Option<ptr<H>>` shapeとしてのcompletionは許可しない。graph criterionの説明例を新しいsource admissionにしない。

## FORMAL findings と non-goals

- **FORMAL-ENCODING**: declaration identity/phaseとruntime identityを独立の小sliceにした。propertyにはexact completion certificateを要求し、phase recordの存在だけから成功を推論しない。selected graphのcycle guardはexact shapeから導出可能という論理的redundancyを明示する。
- **FORMAL-LEMMA**: containment rank、ptr barrier、depth-2 finite derivation、one-completion staging、atomic publication、bounded permutation invarianceをmachine-checkした。
- **FORMAL-SCOPE**: parser、names/ID allocator、full compiler registry/rollback、nominal restriction、mutual/general recursive source、object graph、field mutation、allocation、production refinementは未実装。本boundからaddabilityを否定しない。
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION**: 照合したcanonical ruleに発見なし。規則の追加・補完・Draft編集なし。

No source syntax design、compiler implementation、runtime recursive Node、Node field mutation、allocation、cJSON、general recursive type/generic frontend、FFI/separate compilation、F3.1。

## Verification / review handoff

- exact main baseline: `lake build` PASS（777 jobs）、`bash scripts/check-proofs.sh` **1079 PASS**。
- branch: `lake build` PASS（780 jobs）。45 general declarations + 25 controlsを追加。既存1079件を順序どおり保持し、**1149 declarations**をaudit。
- project-owned Lean sourceにproof placeholderなし。custom semantic axiomなし。許可logicは既存の `propext`、`Classical.choice`、`Quot.sound`のみ。
- Lean `v4.34.1` / mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` / manifest / bootstrap / workflowは不変。
- exact final headのpull_request `Lean proofs`結果とPR URLはIssue #33の `Track: F` handoff / PR本文へ記録する。local結果だけをremote CI成功としない。
- PRはOPEN / unmergedでCoordination reviewへ渡し、後続実装を始めない。

Stop marker（exact-head CI確認後）: **F RECURSIVE-NOMINAL COMPLETION ADJUNCT READY FOR REVIEW**。

## Audited declaration inventory

以下の70 public declarationsを追加する。private fixture/proof helpersも通常のkernel buildで検証する。


### `NewLang.Declaration` — 45 declarations

Source: [NewLang/Declaration/Proofs.lean](../NewLang/Declaration/Proofs.lean)

- `selected_shape_has_no_value_cycle`
- `ptr_target_is_not_containment`
- `ptr_barrier_stops_every_nonempty_containment_path`
- `ptr_has_typed_target`
- `option_link_reaches_only_the_ptr_barrier`
- `direct_value_cycle_is_rejected`
- `option_without_ptr_barrier_has_value_cycle`
- `completion_preserves_nominal_identity`
- `completion_preserves_field_labels`
- `completion_commits_exact_fields`
- `completion_rejects_identity_substitution`
- `completion_rejects_value_cycle`
- `complete_header_cannot_complete_again`
- `completion_occurs_once`
- `incomplete_header_is_not_another_completed_declaration`
- `complete_function_iff_step`
- `repeated_option_ptr_instantiation_has_exact_type_identity`
- `ptr_capabilities_ignore_target_completion`
- `option_composes_any_payload_property`
- `option_ptr_capabilities_ignore_target_completion`
- `incomplete_nominal_property_query_is_rejected`
- `selected_completion_has_finite_property_derivation`
- `nominal_property_requires_exact_completion`
- `ptr_formation_preserves_runtime`
- `ptr_formation_does_not_mint_incarnations_or_provenance`
- `completion_does_not_mint_runtime_objects`
- `incomplete_header_cannot_be_published`
- `two_completion_requests_fail_staging`
- `unresolved_final_header_cannot_register`
- `failed_registration_keeps_public_snapshot`
- `duplicate_completion_cannot_publish_partial_success`
- `invalid_completion_keeps_public_snapshot`
- `exact_completion_can_register`
- `already_complete_header_cannot_register`
- `public_success_has_exact_completed_stage`
- `public_registration_requires_initial_incomplete_header`
- `registration_success_requires_one_exact_completion`
- `staging_preserves_nominal_identity`
- `publication_preserves_nominal_identity`
- `publication_commits_exact_selected_types`
- `header_membership`
- `header_collection_is_order_independent`
- `declaration_occurrence_count_is_order_independent`
- `bounded_admission_is_order_independent`
- `collection_consumer_is_order_independent`

### `NewLang.Declaration.Counterexample` — 25 declarations

Source: [NewLang/Declaration/Counterexample/Completion.lean](../NewLang/Declaration/Counterexample/Completion.lean)

- `selected_node_shape_is_legal`
- `selected_node_registration_succeeds`
- `ptr_and_option_properties_exist_before_header_completion`
- `selected_node_copy_and_discardable_have_finite_derivations`
- `direct_by_value_cycle_cannot_complete`
- `missing_ptr_barrier_cannot_complete`
- `treating_ptr_target_as_containment_creates_false_cycle`
- `selected_path_stops_at_ptr_without_unfolding_header`
- `duplicate_exact_completion_is_rejected`
- `inconsistent_second_completion_is_rejected`
- `different_declaration_cannot_substitute_header_identity`
- `same_header_cannot_commit_another_nominal_ptr_target`
- `duplicate_field_labels_cannot_complete`
- `field_order_identity_cannot_be_substituted`
- `unresolved_field_cannot_commit`
- `empty_registration_cannot_publish_incomplete_header`
- `failed_second_completion_preserves_prior_public_snapshot`
- `ptr_type_formation_does_not_create_value_or_provenance`
- `completion_does_not_create_value_or_provenance`
- `ptr_property_does_not_admit_unknown_type_formation`
- `pointer_only_link_is_not_the_exact_selected_profile`
- `forged_complete_phase_cannot_skip_registration_validation`
- `bounded_header_collection_does_not_depend_on_body_position`
- `bounded_completion_result_does_not_depend_on_body_position`
- `collecting_a_set_alone_would_hide_duplicate_declarations`
