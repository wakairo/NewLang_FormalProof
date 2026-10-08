# Bounded known-call tail owner conservation adjunct

Track: F

Issue: [FormalProof #35](https://github.com/wakairo/NewLang_FormalProof/issues/35)

Disposition: **F OVERNIGHT KNOWN-CALL OWNER CONSERVATION EVIDENCE READY FOR COORDINATION REVIEW**.
これは限定的な formal evidence の candidate であり、F3.1、global Safe Core theorem、production correctness の completion claim ではない。

## Authority / baseline

- Compiler current main: `aed9e7b7d49de338c570c8c6e89197f2251db134`。
- 同 SHA の `docs/reference/CURRENT_SPEC.md`: **Draft 17.27**。
- Canonical: `docs/reference/NewLang_v0_spec_Draft17_27.md` §3.1–3.4、§13.5c、§14.5–14.6、§18.1a / §18.2。
- FormalProof current main / base: `6098868e6d4426078bef413a1a2528dbf4f6951c`。
- 開始時の両 live main は Issue の frozen authority と一致した。
- `docs/NewLang_Project_Development_Process.md` を同 Compiler SHA で確認した。
- Historical design-intent gate: **N/A**。既存 canonical の選択された receiver に対する proof encoding であり、source/API/semantic decision を追加しない。
- Baseline: `lake build` 成功（780 jobs）、proof audit **1149 declarations** 成功。
- Lean `v4.34.1`、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、elan/bootstrap/manifest/CI は変更しない。

## 既存 interface と選んだ bound

F0 Domain/WellFormed は domain identity と value carrier を分離し、domain transfer が governing root を変えない。
F1 Backing/Occupancy は root、empty slot、raw Storage の責任を区別し、abstract region/byte/extent により full-range と disjointness を表す。
F2 は fresh binding と affine carrier の保存を扱うが、known direct function evaluator ではない。
F3 Memory の rich sum lifetime adapter は **one root / one region / one claim** に限定されている。
既存 F3 global contract は実装済み global theorem ではない。

今回の additive `NewLang.Adjunct.KnownCall` は、その型・責任の区別を使う**別の有限 snapshot model**である。
既存 F0/F1/F2/F3 の state や public theorem を変更しない。
既存モデルとの full operational simulation を証明したとは主張しない。

- two already-live roots: head と tail。追加 allocation / initialize / third root の rule はない。
- 同じ completed H の全 occupancy を一つの full-range extent に集約する。
- 各 root の location/place/incarnation/current fact/package/domain/extent は固定 context に置く。
- `ContextValid` は各 identity の分離、正の同一 type size、元 region の full range、byte footprint の disjointness を要求する。
- 各 original region の occupancy responsibility は `typed → emptySlot → raw → released` の単一 phase。
  typed root と同時に raw claim を所有できないことは representation 上の排他性である。
  fragment/split を認めない、この profile の明示的な bound である。
- Allocation と Domain の value carrier は独立した role→optional `F2.BindingId`。
  occupancy は Allocation value の carrier ではない。
- `WellFormed` は carrier availability / domain liveness / release count / fresh-history recording / carrier uniqueness / surviving dependencies を検査する。
- `usedBindings` と release count は proof-only ghost state。runtime metadata の要求ではない。

**Formal representation choices are non-normative.**

## Entry と conditional receiver evidence

`RequiredAtEntry(c,s,args)` は未証明の有限 relational predicate である。
型が `ptr<H>, Allocation, LifetimeDomain` であるだけでは成立しない。

検査対象は二つの live roots、tail の exact ptr location/incarnation、ptr evidence region、
source-founded issued-token set と readable-region set、Allocation の元 region/carrier、
Domain の同一 identity/carrier、value/root/domain/region の scope blockers の不在、
H の static discardability、明示 platform precondition である。

`ContextValid` と pre `WellFormed` も call 側の別義務である。
matching full range は型名や numeric address から推測しない。
`FreshParameters` は二つの未使用で異なる parameter binding IDs と、その新 carrier に対する conflict 不在を検査する。
heap root incarnation はその新 binding ID と別の型・別の identity である。

`transfer` は tail の既存 Allocation/Domain の保存場所だけを変更する。
元 carrier は全 role から消え、同じ R_t/D_t と typed O_t が残る。
Copy ptr のコピーは state を変えず、Allocation/Domain/Storage を生成しない。

receiver は固定された strict sequence:

```text
EndRoot(tail)
  -> same-H empty slot
  -> erase_slot / full original R_t Storage
  -> finalize same D_t
  -> consume same A_t and Storage / end R_t
  -> unit
```

`matched_receiver_primitive_applicability` が各段の gate を導出する。
`Can*` はこの固定された `Call` の段階条件であり、任意の snapshot に単独で適用できる general safe primitive API ではない。
raw candidate 関数は条件を無視して評価できるが、それ自体は legal step ではない。
read access は選択された optional scoped-read receiver 用の entry obligation として保持し、source-level read/loan evaluator 自体は追加しない。
`strict_recovery_order` と `recovery_is_original_full_range` が同じ extent の回復を示す。
`call_conserves_exact_region_responsibility` は、終了時の head footprint と解放された元 tail footprint が entry の全責任を正確に分解し、互いに disjoint であることを証明する。
解放された region を「生きた責任」として残すのではなく、一回の release event として記録する。

`receiver_preserves_wellFormed` / `known_call_preserves_wellFormed` は **post WellFormed を premise に含まない**。
pre invariant、entry、fresh carrier、exact survivor guard から導出する。
これは選択された有限 receiver の conditional body evidence であり、任意の関数の独立 definition checker の実装ではない。
実 call を受理するには、その caller snapshot に対して entry の全項目を別途証明する必要がある。
`Call` は entry 失敗時の遷移を持たない。failure handling の frontend transaction はモデル外である。

## Dependency / scope / stale ptr

この slice の blocking facts は F0 の exact `ValueFact(place,id)` と `DomainLive(id)`。
head package と external survivor の dependency data は書き換えない。
`SurvivorGuard` はそれらが ended tail current fact または finalized tail domain に依存しないことを要求する。
消費される tail package 自身の dependency は guard の対象外となる。

concrete positive control は、tail だけが tail current fact と D_t に依存する場合も destroy receiver を通せる。
head/external survivor に同じ依存があれば call は存在しない。
negative controls の pre-state 自体も `WellFormed` を満たすため、reject は壊れた input による vacuous なものではない。
guard を省くと、存続 head が死んだ fact に依存する malformed post-state ができる。

issued ptr token は終了後も記録に残すが、`CurrentLocator` は original root の終了により成立しなくなる。
ptr provenance を blocking dependency と自動的に同一視しない。
selected value/root/domain/region scope blockers は entry で検査し、carrier移転で削除しない。

## Positive / negative controls

- Proven matched entry と two-root call witness。
- head live / tail ended / tail region released once、head authority 保存。
- tail old-only current/domain dependency の atomic consumption。
- `ptr_h,A_t,D_t` reject。
- `ptr_t,A_h,D_t` reject。
- `ptr_t,A_t,D_h` reject。
- 同じ region でも carrier が違えば reject。
- 正しい場所でも stale incarnation は reject。
- provenance / backing access の欠如は reject。
- scope conflict、historical parameter reuse、同じ二 parameter ID は reject。
- typed occupancy の early deallocate、head Allocation による tail Storage 解放、non-full raw fragment は reject。
- 二回目の EndRoot/finalize/deallocate は reject。
- non-Discardable current root は destroy receiver entry を満たさない。
- head / external current fact / external domain dependency は reject。
- entry を無視する eager handoff は caller carrier を変更する。
  この handoff の post が局所 `WellFormed` でも、mismatched entry の正当化にはならない。
- dependency guard を省く receiver は dependency preservation を破る。

## 未証明の adapter / 必要な前提

限定 adjunct の保存結果から、production の H caller を直ちに safe と判定してはならない。
次は具体的な未証明 interface であり、隠れた追加 canonical law ではない。

1. **Source-founded caller snapshot**: 二つの実 allocate/initialize 結果から `ContextValid`、各 original owner/carrier、issued provenance、access、full occupancy をこの snapshot に写す adapter。
   本 module は allocator/initialize を実行せず、成功済みの snapshot を入力とする。
2. **H fixed children / Option link occurrences**: actual H 全体の child incarnation/current facts、Option occurrence/payload facts を `Ended`/survivor guard に接続する two-root adapter。
   今回は root-current/domain facts のみを扱う。occurrence fact を erase して reverse legality を推論しない。
   H の link detach、before-call Change/Reset、occurrence dependency を含む caller の受理は未証明。
3. **General ledger projection**: F1 fragment-capable `Accounting` の claim set / physical world が、この単一 full-range phase に対応し、他の outstanding raw/slot claim が無いという sound projection。
   `Ledger.scope` を Allocation authority と解釈してはいけない。
4. **Scope/access/platform grounding**: actual loan scopes、representation/provenance、allocator preconditions が有限 blocker/access/platform snapshot の predicates を満たすこと。
   数値一致や human assertion はこの証拠の代わりではない。
5. **Checker/body refinement**: 独立 definition checking の inferred entry obligation と strict body effect、全 matched known call sites の discharge を、この conditional receiver evidence に結び付ける refinement。
   arbitrary function、argument evaluation side effects、exceptions/early return、ABI/backend は証明しない。

このため「現行 F0〜F3 に対する full H operational adapter 経由の同じ主張」はまだ証明不能である。
今回の成果は、上記 snapshot 前提が満たされた場合の二-root conservation と、その前提を省いた具体的失敗の限定 proof adjunct である。
不足する premise を post-WellFormed や coarse→rich legality で埋めていない。

## FORMAL findings / scope

- **FORMAL-ENCODING**: finite role carrier / phase representation、fixed execution context、ghost binding history / release count。
  Allocation は occupancy/ptr/domain と別の責任として表現する。
- **FORMAL-LEMMA**: matched transfer は root/governing identity を保存し、receiver は pre invariant / survivor guard から post invariant を導く。
  entry 証明を handoff 後の WellFormed で代替できない rollback control を追加した。
- **FORMAL-SCOPE**: 上記 five adapter interfaces は未証明。F3.1、general owner/effect contract、general function semantics へ進まない。
- **FORMAL-HOLE / FORMAL-AMBIGUITY**: inspected §3.2 / §13.5c / §14.5 / §18.1a には今回の slice を阻止する canonical contradiction を発見しなかった。
- **FORMAL-EXTRACTION**: canonical/bridge 修正は不要。

same-unit known-direct synchronous nonrecursive receiver / two already-live roots / one tail owner transition のみ。
first/second allocation failure、third root、recursive deletion、cJSON、P native #197、source-visible contracts、general allocation、M/P/R/V、LLVM、FFI、modules、concurrency は変更・実装しない。

## Verification / review handoff

- `lake build`: **PASS**, 783 jobs。
- `bash scripts/check-proofs.sh`: baseline 1149 を全て保持し **64追加 / 1213 declarations** を audit。
- Project-owned Lean の proof placeholders は無し。標準 logic の許可範囲は従来の `propext`, `Classical.choice`, `Quot.sound` のみ。
- New modules は default `NewLang` import に含まれ、CI が controls も build/audit する。
- pins / existing `Lean proofs` workflow は不変。候補 branch `f-known-call-owner-conservation`、PR は OPEN / unmerged。
- PR-triggered CI の run URL と exact head SHA の確定 receipt は Issue #35 / PR に記録する。
  report に自己参照の commit SHA を埋め込まない。

## Audited declaration inventory

追加64宣言（private fixture helperは含めない）。

```text
NewLang.Adjunct.KnownCall.copy_ptr_grants_no_authority
NewLang.Adjunct.KnownCall.transfer_preserves_memory
NewLang.Adjunct.KnownCall.transfer_preserves_exact_responsibility
NewLang.Adjunct.KnownCall.transfer_records_fresh_parameters
NewLang.Adjunct.KnownCall.transfer_consumes_donor
NewLang.Adjunct.KnownCall.transfer_preserves_wellFormed
NewLang.Adjunct.KnownCall.receiver_effect
NewLang.Adjunct.KnownCall.strict_recovery_order
NewLang.Adjunct.KnownCall.recovery_is_original_full_range
NewLang.Adjunct.KnownCall.receiver_dependencies_valid
NewLang.Adjunct.KnownCall.receiver_preserves_wellFormed
NewLang.Adjunct.KnownCall.transferred_entry
NewLang.Adjunct.KnownCall.known_call_preserves_wellFormed
NewLang.Adjunct.KnownCall.call_ends_only_original_tail
NewLang.Adjunct.KnownCall.known_call_cannot_double_release
NewLang.Adjunct.KnownCall.known_call_preserves_head_authorities
NewLang.Adjunct.KnownCall.matched_receiver_can_deallocate
NewLang.Adjunct.KnownCall.release_rejects_nonfull_or_other_region
NewLang.Adjunct.KnownCall.typed_root_cannot_release
NewLang.Adjunct.KnownCall.entry_rejects_wrong_ptr
NewLang.Adjunct.KnownCall.entry_rejects_wrong_allocation_region
NewLang.Adjunct.KnownCall.entry_rejects_wrong_domain
NewLang.Adjunct.KnownCall.entry_rejects_absent_donor
NewLang.Adjunct.KnownCall.entry_rejects_scope_conflict
NewLang.Adjunct.KnownCall.transfer_preserves_governing_and_locator
NewLang.Adjunct.KnownCall.matched_receiver_primitive_applicability
NewLang.Adjunct.KnownCall.matched_transfer_keeps_original_root
NewLang.Adjunct.KnownCall.ended_tail_fact_and_domain_not_live
NewLang.Adjunct.KnownCall.ended_tail_ptr_cannot_reacquire
NewLang.Adjunct.KnownCall.rejected_entry_has_no_call
NewLang.Adjunct.KnownCall.surviving_ended_dependency_has_no_call
NewLang.Adjunct.KnownCall.parameter_bindings_are_consumed_at_return
NewLang.Adjunct.KnownCall.call_conserves_exact_region_responsibility
NewLang.Adjunct.KnownCall.call_preserves_dependency_data
NewLang.Adjunct.KnownCall.Counterexample.matched_entry_is_provable
NewLang.Adjunct.KnownCall.Counterexample.independent_two_root_call_exists
NewLang.Adjunct.KnownCall.Counterexample.original_head_live_tail_released_once
NewLang.Adjunct.KnownCall.Counterexample.head_ptr_tail_owners_rejected
NewLang.Adjunct.KnownCall.Counterexample.tail_ptr_head_allocation_rejected
NewLang.Adjunct.KnownCall.Counterexample.tail_ptr_head_domain_rejected
NewLang.Adjunct.KnownCall.Counterexample.stale_tail_ptr_rejected
NewLang.Adjunct.KnownCall.Counterexample.unchecked_handoff_before_entry_breaks_rollback
NewLang.Adjunct.KnownCall.Counterexample.same_region_wrong_carrier_rejected
NewLang.Adjunct.KnownCall.Counterexample.typed_occupancy_cannot_be_deallocated
NewLang.Adjunct.KnownCall.Counterexample.recovered_tail_storage_cannot_release_head_allocation
NewLang.Adjunct.KnownCall.Counterexample.double_release_rejected
NewLang.Adjunct.KnownCall.Counterexample.historical_parameter_binding_reuse_rejected
NewLang.Adjunct.KnownCall.Counterexample.ending_scope_conflict_rejected
NewLang.Adjunct.KnownCall.Counterexample.old_only_dependency_consumed_by_receiver
NewLang.Adjunct.KnownCall.Counterexample.surviving_head_dependency_rejects_receiver
NewLang.Adjunct.KnownCall.Counterexample.external_current_dependency_rejects_receiver
NewLang.Adjunct.KnownCall.Counterexample.external_domain_dependency_rejects_receiver
NewLang.Adjunct.KnownCall.Counterexample.unchecked_receiver_breaks_dependency_preservation
NewLang.Adjunct.KnownCall.Counterexample.mismatched_entry_cannot_grant_even_if_handoff_wellFormed
NewLang.Adjunct.KnownCall.Counterexample.head_dependency_prestate_is_wellFormed
NewLang.Adjunct.KnownCall.Counterexample.head_dependency_has_no_call
NewLang.Adjunct.KnownCall.Counterexample.external_dependency_prestate_is_wellFormed
NewLang.Adjunct.KnownCall.Counterexample.external_dependency_has_no_call
NewLang.Adjunct.KnownCall.Counterexample.absent_provenance_rejected
NewLang.Adjunct.KnownCall.Counterexample.absent_backing_access_rejected
NewLang.Adjunct.KnownCall.Counterexample.nondiscardable_tail_rejected
NewLang.Adjunct.KnownCall.Counterexample.duplicate_parameter_carrier_rejected
NewLang.Adjunct.KnownCall.Counterexample.nonfull_raw_fragment_rejected
NewLang.Adjunct.KnownCall.Counterexample.no_second_end_or_finalize
```
