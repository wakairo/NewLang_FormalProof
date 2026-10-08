# Track F — Draft17.28 live-tail RETURN conservation adjunct

対象は [FormalProof Issue #37](https://github.com/wakairo/NewLang_FormalProof/issues/37) の有限モデルのみ。
**F DRAFT17.28 LIVE-TAIL RETURN CONSERVATION READY FOR COORDINATION REVIEW** の候補証拠であり、独立 Coordination review 前の仕様承認・merge・F3.1 完了を意味しない。

## Authority と運用

- Compiler main: `ff9098848dc6a826d6a8be84c2f33dce9e9b393c`。
- `docs/reference/CURRENT_SPEC.md` → canonical `NewLang_v0_spec_Draft17_28.md`、§§18.1b.1–6。§18.1a / §13.5c / §14.5 / §20.4 も参照。
- FormalProof base main: `ce6d117ccd71ba19f90c07bdade67309893f70b1`（PR #36 merge 後）。
- Compiler の Development Process §§2 / 4.2 / 6 / 7 / 9、Design Decision Procedure、Ledger DI-009–012 を照合。historical design audit: **N/A — faithful formalization of adopted §18.1b; no new language semantics**。DI-012 の adopted/bounded selection を証拠化する。
- P #210 の未merge branch・emitter に依存しない。Compiler、canonical Draft、他 Track は変更しない。
- branch `f-live-tail-return-conservation`、候補 PR は OPEN / unmerged。Issue の substantive handoff は `Track: F`。正確な candidate SHA、PR、pull-request-triggered CI receipt は PR / Issue #37 で記録する。

## terminal #35 との相違

#35 の `KnownCall.callPost` は O_t を終了し D_t を finalize、R_t を解放する。今回の `producerPost` はそれを呼ばず、O_t は typed、D_t は live、full R_t の state-owned root responsibility はそのまま残る。`earlier_terminal_post_is_not_still_live_return` は前者を LiveTail と再解釈できないことを示す。

producer から caller へ渡るのは元の Allocation / LifetimeDomain **値の carrier** と Copy ptr provenance。heap root・BackingRegion・Domain identity を新しい package placement に作り直さない。LiveTail は三つの field の semantic envelope であり、Storage / slot や heap placement を含まない。

## 有限 state / caller evidence

`NewLang/Adjunct/LiveTail.lean` は既存 `KnownCall.Context/State` に head link の conditional occurrence、field current fact、precise dependency、lexical scope、result custody を加える。既存 F0/F1/F2/F3 public theorem と #35 implementation は変更しない。

- 二つの already allocated/current complete roots。同じ有限 H profile、different O/R/D、full extent、disjoint abstract byte footprint。
- committed head field の固定 place/incarnation と current `Some(world, ptr_t)`。layout は root と区別し、current tail ptr / provenance / access と一致させる。
- `WorldId` は proof-only qualifier。ptr 数値 ID が同じでも別 world の argument/ref/Some payload は一致証拠にしない。
- precise fact は既存 conditional `Fact`（root / fixed field / occurrence / payload value）。blocking semantic dependency と issued persistent ptr provenance は別。ptr に occurrence blocker を自動追加しない。
- `usedBindings`、`usedFacts`、`usedOccurrences` と release count は ghost state。lexical scope binding も歴史へ記録し、現在 live でなくなっただけの binding を再利用しない。runtime counter/history set を要求しない。

`ActualCallApplicable` は pre-WellFormed、ContextValid、donor state、matching world、既存 §18.1a の `RequiredAtEntry`、正確な head ref / D_h / scope / read+write access / Some(ptr_t)、fresh binding/fact plan、`DetachGuard` と `ResultNonescape` を要求する。tail 側は既存 finite receiver-compatible H profile の discardability/platform/full-range-recovery 条件も保持する。これは任意の nonDiscardable H producer への一般化ではない。

`ResultNonescape` はこの有限 scope model で、返す input owner fields に head scoped capability dependency がないという明示的な入力 guard。constructor は head ref を field に含めず、input ptr/A/D dependency data をそのまま保持する。ここでは source checker がその guard を infer/discharge することを証明していない。

## 定義時の conditional contract と actual call

`DefinitionChecked` は selected body の semantic skeleton `detach → construct [ptr, allocation, domain] → return` を検査する。`selected_producer_definition_is_conditional` は geometry のみに依存し、任意の uncorrelated state/ref/arguments に対して、上記相対 obligation が成立した場合の preservation / complete result を証明する。具体的な main を選んで有利な identity を仮定しない。

これは full source definition checker ではない。実際の constructor/type/scope inference、左から右の expression evaluation は adapter 境界。三つの selected fields の順序・完全性と atomic publication は skeleton / candidate で表す。actual call ではすべての entry/guard を別途 machine-check する。`definition_certificate_does_not_grant_mismatched_entry` は定義 certificate があっても wrong D_t の call を許可しない。

## Producer の semantic trace

1. 元の available A_t/D_t donor bindings → fresh formal bindings。
2. head Change/Reset: `Some(ptr_t) → None`、old link occurrence/payload fact と old head/field current fact が終了。fresh parent/field fact を歴史へ追加。head root place/incarnation/R_h/D_h と tail の全 root identity/cell は保持。
3. formal A_t/D_t → local LiveTail field carriers → fresh returned LiveTail field carriers。package placement はそれぞれ fresh lexical binding であり O_t ではない。
4. head scope を guard 付きで閉じる。known return origin を持つ package のみ whole destructure し fresh caller A/D bindings へ移す。bundle は消え、二度目の destructure は拒否。

carrier table は唯一の責任 ledger。bundle の A/D field は同じ carrier entry の view であり二重登録ではない。`producer_preserves_original_responsibilities` / `producer_donor_carriers_consumed` / `producer_no_direct_donor_or_formal_owner` で保存・donor 消費・bundle custody を証明する。post-WellFormed は入力 premise にせず、pre invariant、freshness、survivor guard、既存 transfer preservation と head fact 更新から導出する。

`Bundle.copyable` / `discardable` は field capability の conjunction。Copy ptr と nonCopy/nonDiscardable A/D から両方 false。constructor field の欠落・重複、duplicate return carrier、tail を内部で finish する body は拒否する。

## 後段 receiver / head cleanup

whole destructure 後に改めて `TerminalCall` を検証する。これは既存 #35 `KnownCall.Call` の実際の applicability / survivor guard に、precise dependency guard と unpacked custody を加えたもの。nominal LiveTail 型または coarse signature だけから terminal permission を得ない。

positive witness は原 ptr_t / R_t / D_t で tail EndRoot→slot→Storage→finalization→deallocation を行い、release count = 1、head は live、A_h/D_h は保存。tail ptr は current locator でなくなり、second release / root resurrection は拒否。

tail current fact を観測する外部 survivor のある pre-state では **producer は legal / terminal は reject** (`live_return_is_not_an_automatic_terminal_grant`)。producer preservation を terminal receiver の一般適用可能性に置き換えない。

caller の別途 head cleanup は具体例で示す。view の head/tail role を permutation して元の A_h/D_h / full R_h を使い、各 `CanEnd / CanEraseSlot / CanFinalize / CanDeallocate` をその時点で証明する。root を移動する操作ではない。旧 #35 `Call` は both-roots-live entry に限定されるため、tail 終了後に逆向きでその Call を再利用したとは主張しない。final snapshot は両 root が一度ずつ released、carrier なし、rich/owner accounting WellFormed。

## Positive / negative controls

同じ concrete snapshot から producer return、scope exit、whole destructure、独立 receiver、別途 caller cleanup を通す。O_h/R_h/D_h と O_t/R_t/D_t はそれぞれ 1 / 2、head field identity は 3、head scope 99、old link occurrence 7。retired fact 90 を history に残す。formal / local / return / unpack / terminal の carrier IDs は全て別で、heap identity はそのまま。

- positive: 完全な still-live result、tail と head の保存、donor/formal/local carrier 消費、scope exit、独立 terminal、両 root 一度ずつの解放。
- nonempty dependency positive: owner の tail DomainLive dependency が return boundary で消去されず、そのまま live。
- negative identities: wrong R/D、head ptr、stale tail incarnation、None / Some(other)、foreign world の引数/ref/Some、wrong fixed field。
- negative access/custody: read-only、expired head scope、head write backing access 欠如、A/D carrier 欠如、head-scope-dependent result、historical fact/binding reuse、duplicate return fields、destructure の二度目、destructure を飛ばす receiver、receiver の再実行。
- negative dependency: ended occurrence / old field fact / old parent fact を持つ survivor、tail の current fact に依存する survivor の terminal 終了。
- broken-rule control: detach guard を削除すると owner accounting は成立しても ended occurrence dependency が残り `DependenciesValid` が破れる。Some だけ消して occurrence を残す candidate は shape invariant に反する。
- failed definition/call は `checkedProducer` の public snapshot と certificate を `(pre, none)` に保つ。これは classical な publication specification であり executable checker、expression exception、allocation failure/OOM rollback の証明ではない。

## Clause 対応

| Canonical | 有限証拠 |
| --- | --- |
| §18.1b.1 | exact ordered 3-field skeleton、field-derived Copy/Discardable false、whole destructure、no Storage/root placement in bundle |
| §18.1b.2 | conditional definition / separate actual entry、preservation derived from pre、O/R/D correlation、nonescape guard、no donor amplification |
| §18.1b.3 | formal → local → return → caller bindings、unchanged dependency data、known-return origin、independent terminal applicability |
| §18.1b.4 | both-Some branch の current head link → None、still-live original tail return、scope exit、terminal と head cleanup の concrete path |
| §18.1b.5 | identity/access/scope/constructor/custody/dependency negatives、no signature-only grant |
| §18.1b.6 / §20.4 | closed finite evidence、production checker/native implementation は未証明、hidden human proof を compiler permission としない |

## FORMAL findings / 未モデル化境界

- **FORMAL-ENCODING:** two-root ledger の additive precision overlay と one-bundle custody。world tags、fresh carrier placements、history は非normative。旧 #35 terminal theorem から still-live return を推論しない。
- **FORMAL-LEMMA:** detach の exact ended-fact guard から rich dependency retention、owner/history conservation と post invariant を導出。return と terminal で survivor 集合が異なり、後者は別 guard が必要。
- **FORMAL-SCOPE:** concrete head cleanup のみ。一般 remaining-root direct-call adapter、arbitrary owner API / multi-root allocation / recursive producer / unknown/indirect call / OOM は対象外。
- **FORMAL-SCOPE:** committed H field/layout と two-root snapshot の caller grounding は前提。Declaration completion、F1 full structural/current-sum world、field projection/ref acquisition、loan checker と Blocker、byte layout/full program semantics への operational/refinement adapter は未証明。全 F0/F1/F2/F3 integration ではない。precision-losing erasure の逆向き legality を使用しない。
- **FORMAL-SCOPE:** actual source AST / production checker / checked emission / malloc/free / physical memory / C17 native / cJSON reference policy / frozen North Star / general ABI は未証明。P #210 を検証したとは主張しない。
- **FORMAL-HOLE / FORMAL-AMBIGUITY:** この finite slice に canonical を反証する witness は見つからなかった。上記 source/operational interfaces の省略を新しい normative assumptions に変換しない。

## Frozen verification

Lean/Lake `leanprover/lean4:v4.34.1`、elan `4.2.4`、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`。toolchain / lakefile / manifest / bootstrap / workflow を変更しない。
Baseline main: `lake build` PASS (783 jobs)、proof audit PASS (1213 declarations)。
Candidate: default `NewLang` imports に new proofs/controls を加えて `lake build` と `bash scripts/check-proofs.sh` を実行。audit は旧1213件を全て保持し、追加 **93件（一般40 + controls53）、合計1306件**。placeholder 禁止と `propext / Classical.choice / Quot.sound` の既存 whitelist を維持する。

Local `lake build` は PASS (786 jobs)、proof audit は PASS (1306 declarations)。既存 `Lean proofs` workflow の pull_request run を exact candidate HEAD で確認し、run URL / SHA / 結果を PR と Issue #37 に添付する。CI receipt を得るまで handoff を完了扱いにしない。候補 PR は OPEN / unmerged で停止し、次の task は開始しない。

## Audited theorem inventory

全て default build と `#print axioms` の対象。private helper は public theorem の kernel proof dependencies に含まれる。

### General proofs

[NewLang/Adjunct/LiveTailProofs.lean](../NewLang/Adjunct/LiveTailProofs.lean)

- `fresh_formal_parameters`
- `fresh_return_fields`
- `producer_preserves_wellFormed`
- `producer_original_tail_and_head_live`
- `producer_changes_head_link_and_parent_fact`
- `producer_returns_complete_original_owner`
- `producer_no_direct_donor_or_formal_owner`
- `producer_result_does_not_escape_head_scope`
- `rejected_call_preserves_public_state`
- `selected_producer_definition_is_conditional`
- `producer_preserves_context`
- `producer_preserves_original_responsibilities`
- `producer_donor_carriers_consumed`
- `producer_packet_uses_actual_original_values`
- `producer_old_link_occurrence_ended`
- `producer_parent_and_link_facts_fresh`
- `producer_tail_still_current`
- `producer_retains_tail_requirements`
- `scope_exit_preserves_wellFormed`
- `known_return_after_scope_is_wellFormed`
- `whole_destructure_preserves_wellFormed`
- `whole_destructure_consumes_package`
- `whole_destructure_cannot_repeat`
- `whole_destructure_preserves_tail_correlation`
- `subsequent_terminal_preserves_wellFormed`
- `subsequent_terminal_ends_tail_once_preserves_head`
- `subsequent_terminal_no_resurrection_or_double_release`
- `actual_call_keeps_head_tail_domains_distinct`
- `wrong_world_rejects_call`
- `wrong_region_rejects_call`
- `wrong_domain_rejects_call`
- `wrong_current_link_rejects_call`
- `readonly_head_ref_rejects_call`
- `expired_head_scope_rejects_call`
- `escaping_owner_dependency_rejects_call`
- `ended_link_dependency_rejects_call`
- `mismatched_bundle_region_has_no_certificate`
- `missing_bundle_domain_carrier_has_no_certificate`
- `ended_root_has_no_live_return_certificate`
- `terminal_receiver_is_not_live_return`

### Concrete witnesses / controls

[NewLang/Adjunct/Counterexample/LiveTail.lean](../NewLang/Adjunct/Counterexample/LiveTail.lean)

- `actual_live_tail_producer_exists`
- `returned_live_tail_preservation`
- `return_has_original_live_identity_and_no_storage`
- `detach_preserves_roots_ends_only_link_occurrence`
- `donor_formal_local_owners_not_duplicated`
- `head_scope_ends_before_result_whole_destructure`
- `returned_packet_cannot_be_unpacked_twice`
- `independently_applicable_subsequent_receiver`
- `terminal_ends_original_tail_once_and_keeps_head_live`
- `terminal_cannot_resurrect_or_double_free`
- `wrong_domain_rejected`
- `wrong_region_rejected`
- `head_ptr_is_not_tail_owner`
- `stale_tail_incarnation_rejected`
- `none_head_link_rejected`
- `other_some_head_link_rejected`
- `foreign_world_numeric_identity_rejected`
- `foreign_head_ref_rejected`
- `wrong_fixed_field_rejected`
- `readonly_head_ref_rejected`
- `expired_scope_rejected`
- `missing_head_write_access_rejected`
- `copied_ptr_cannot_mint_missing_owners`
- `unavailable_domain_owner_rejected`
- `head_scoped_dependency_cannot_escape_in_owner`
- `old_occurrence_survivor_is_live_but_rejects_return`
- `old_field_current_dependency_rejected`
- `old_parent_current_dependency_rejected`
- `historical_fact_reuse_rejected`
- `duplicate_result_field_carrier_rejected`
- `missing_constructor_field_rejected`
- `duplicate_constructor_field_rejected`
- `finishing_tail_is_not_live_return_definition`
- `rejected_actual_entry_does_not_publish_or_consume`
- `bad_constructor_does_not_publish_or_consume`
- `nominal_bundle_cannot_certify_wrong_original_region`
- `nominal_bundle_cannot_supply_missing_domain_carrier`
- `earlier_terminal_post_is_not_still_live_return`
- `still_live_tail_dependency_is_not_terminal_permission`
- `unchecked_detach_breaks_occurrence_dependency`
- `clearing_some_without_ending_occurrence_breaks_shape`
- `caller_can_separately_end_and_release_head`
- `separate_cleanup_releases_each_original_root_once`
- `separate_cleanup_preserves_accounting`
- `live_return_is_not_an_automatic_terminal_grant`
- `returned_owner_keeps_a_nonempty_live_dependency`
- `live_head_binding_cannot_be_reused_for_return`
- `each_producer_boundary_retains_original_tail`
- `unchecked_detach_keeps_owners_but_breaks_dependencies`
- `definition_certificate_does_not_grant_mismatched_entry`
- `caller_final_snapshot_wellFormed`
- `receiver_cannot_bypass_whole_destructure`
- `receiver_cannot_run_again`
