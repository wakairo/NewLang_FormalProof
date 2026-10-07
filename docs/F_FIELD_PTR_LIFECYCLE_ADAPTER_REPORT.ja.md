# Field-aware ptr acquisition / fixed-tree EndRoot adapter

Track: F

## Authority と対象

[FormalProof Issue #31](https://github.com/wakairo/NewLang_FormalProof/issues/31) の F-A〜F-H だけを扱う。作業開始時に Compiler main の [開発運用方針](https://github.com/wakairo/NewLang_Compiler/blob/12d49d049aae6831ce42a7a0b7b55934f01d9a2a/docs/NewLang_Project_Development_Process.md) を読み、双方の main を確認した。

| Authority | 確認した revision |
| --- | --- |
| Compiler main | `12d49d049aae6831ce42a7a0b7b55934f01d9a2a` |
| CURRENT_SPEC | [Draft 17.20](https://github.com/wakairo/NewLang_Compiler/blob/12d49d049aae6831ce42a7a0b7b55934f01d9a2a/docs/reference/NewLang_v0_spec_Draft17_20.md) |
| FormalProof base main | `8d7026970cda1cd5689d73025f40d5c8ac6cb5fd` |
| Branch | `f-field-ptr-lifecycle-adapter` |

Draft §3.8、§10.1–2、§14.2–4、§17.4 と既存 F0/F1 を照合した。新しい P implementation branch は proof input に使わない。Draft 17.4 の historical snapshot と canonical 文書は変更しない。言語全体の safety、production checker correctness、backend correctness は主張しない。

**Formal representation choices are non-normative.** root/site/path/identity の追加 record は mathematical token であり、C address、ABI、runtime field layout、hidden runtime counter の要求ではない。

## F-A — gap inventory と composition

| 既存 layer | 再利用するもの / bounded gap |
| --- | --- |
| F0 `Reference` / `StableRoot` | root-only `PtrToken(location, incarnation)` と explicit stability/access による point acquisition。field designation は持たない |
| F1 `Structural` / `State` / `WellFormed` | `StructuralTarget(location, place)`、finite semantic path、parent/ancestor、exact per-node incarnation、global place/incarnation uniqueness。`LiveNode` は live root support と tracked place の積 |
| F1 `Replace` / `FixedChange` | layout、全 node incarnation、governing relation と fixed support の frame。overlapping current-fact death、survivor dependency rejection |
| F1 `Erasure` | root occupancy / root incarnation / governing domain と coarse obligation を残す。child identity と path precision は失う。child incarnation を root token に渡しても取得できないという既存 theorem は維持 |
| F0 `Lifetime` | raw take/destroy candidate、root incarnation 終了、history recording。今回 root occupancy shadow と既存 ending theorem に接続する |
| F1 `Backing` / `Occupancy` / F3 rich sum lifetime | root-only access evidence、flat Storage/slot lifecycle、conditional rich sum ending は別 slice。任意 fixed descendant tree の geometry/slot transition を既に証明したとは扱わない |

元の二つの FORMAL-ENCODING hook は、field-aware token relation と `CurrentState` 上の最小 root-ending adapter で閉じる。重要なのは、既存 `LiveNode` が enclosing live root を必要とすること。root を live support から除去すれば、固定 child の非live性を導出できる。child lifetime 終了を新しい semantic premise として仮定しない。

## F-B — encoding の比較と選択

| 候補 | 評価 |
| --- | --- |
| F0 `PtrToken` を field/path/parent 情報で拡張し、flat と rich acquisition を統合 | 既存 root-only public interface を変更し、erasure 後にない child 情報も扱う必要がある。この adjunct には大きい |
| F1 の bounded `FieldPtrToken` と、既存 state への exact current-target relation | flat interface を保持し、path/place/child incarnation と enclosing root/site/incarnation を個別検証できる。今回採用 |

`NewLang/F1/Reference.lean` の token は location、root place、root incarnation、semantic path、child place、child incarnation を保持する。path は既存 `List Nat` の projection encoding で、source field grammar や byte offset ではない。root の governing domain は token の authority とせず、acquisition 時に現在の root relation と caller evidence domain を照合する。

`fieldTokenAt` は pure constructor である。Lean value を作れたことから safe source issuance を導かない。`CurrentFieldPtr` は exact live child、proper fixed field、root identity、path、child incarnation を要求する。path だけ、child incarnation だけ、inactive map data だけでは十分でない。

## F-C / F-F — point acquisition と non-amplification

`RawFieldAcquireRef stable access s ptr d` は current-target relation、root governing relation、explicit `stable`、explicit `access` を要求する。`FieldAcquireRef` は pre-state `CurrentWellFormed` を加える。`access` は ordinary permission、typed provenance、representation/backing の省略した obligations をまとめた caller proposition である。write/exclusive/ending authority を token から生成する rule はない。domain liveness は governing relation と既存 WF から導く。

これは F0.5 と同じ **point-of-acquisition** predicate。持続する ref package や lexical future-use scope を新設しない。read acquisition は current-value fact を token に取り込まず、state/package/dependency data を更新しない。current value の読み出し・extraction とそこで導入する dependency は別の既存機構である。従って「acquisition が current-value dependency を発明しない」という claim は、この bounded predicate の fields / audit と old-fact-dead acquisition witness に限る。全 source ref derivation の correctness ではない。

wrong path、child incarnation、parent place/incarnation、site、sibling retargeting、domain、missing stability/access を一般 theorem と concrete controls で拒否する。liveness を省いた broken predicate は inactive root function のデータにも合致するが、正しい acquisition は拒否する。

## F-D — Change との integration

既存 `RawStructuralReplace` の frame theorem を使い、同じ token の current-target relation と pure token identity を保存する。checked field replace の後に再取得するには、**post-state に対する新しい stability/access evidence** が必要である。pre-state の evidence を自動転送する theorem ではない。

既存 nested fixture の `x`（path `[0,0]`）で legal replace を実行すると old `Value(x)` は dead になるが、root/child incarnation と同じ field token は current のままで、明示 evidence の下で acquisition が legal。sibling `y` の Change も `x` token を retarget しない。

一方、取得可能な ptr があることは surviving semantic dependency を取り消さない。returned old field value が `Value(x, oldFact)` に依存する場合は、既存 `FixedChange` rejection をそのまま使って field replace を拒否する。

## F-E — fixed-tree root-ending adapter

`NewLang/F1/FixedLifetime.lean` は `CurrentState` に対する小さい adapter を追加する。

- `endCandidate s l returned` は root site `l` を live support から除去する。layout/node/content の inactive data は保持する。
- take（`returned = true`）は root package を loose carrier に移し、`extractValue` の **exact whole structured value** をそのまま返す。local dependency data を書き換えない。
- destroy（`returned = false`）は old package を返さず、static root discardability を要求する。take の value-read guard は要求しない。
- `RawEndRoot` は live parent、exact governing relation、explicit ending authority、take の ordinary read / destroy の discardability、candidate equation を保持する。child 独立 ending operation は追加しない。
- `EndDependenciesSafe` は other live roots、既存 loose values、take の returned whole value だけを survivor として検査する。destroy で消費する old-only dependency は検査対象に残さない。
- `EndStep` は pre WF + raw relation + exact survivor guard。**post WF を premise にしない。** `end_candidate_wellFormed` が全 structural/carrier/domain/dependency/history invariants、structured loose-data coherence、root capability coherence を導出する。

root とすべての tracked descendant incarnation は live でなくなる。global incarnation uniqueness により、別 root の同じ identity に「逃がす」こともできない。全 old current facts も dead になる。history、domains と他 root の identity は保持する。

old field token は数学的 value として残り、old child identity は history に記録されたまま。しかし root support がなくなったため acquisition は拒否される。concrete control では inactive node の **stored currentFact を全く変えない**まま拒否し、current-value fact mismatch に依存しないことを示す。

### F0 shadow と erasure の方向

rich raw take/destroy から既存 F0 raw root-ending shadow を作り、root **occupancy** の erasure commutation を証明する。parent incarnation 終了は既存 `F0.take_ends_incarnation` / `destroy_ends_incarnation` を再利用する。rich post WF から既存 sound state erasure も利用できる。

全 package table の erasure commutation、exact Step simulation、coarse legal take から rich legal take への逆推論は主張しない。child dependency の precision を失う erasure は rich survivor guard の代用ではない。Storage/slot ledger と任意 fixed tree の lifecycle を接続した full geometry adapter も今回の成果に含めない。

### Same-site fresh restart

`FreshTreeRestart` は inactive site の再activation、history monotonicity、**全 tracked node incarnation の historical freshness**を表す小さい certificate。ordinary root ID の freshness だけでは child token の非復活を証明できないため、必要な whole-tree lifetime-start obligation を明示する。fresh initialize operation、allocator、runtime identity supply は実装しない。

general theorem は recorded old child token が certificate を満たす fresh tree に acquisition できないことを証明する。concrete witness は同じ location / layout / PlaceIds の tree を fresh root/child incarnations と facts で構成し、全 WF を証明する。take result は loose に残す。take/destroy の両経路で new field token は取得可能、old token は取得不能であり、historical child ID reuse は certificate に反する。これは bounded semantic restart witness で、physical placement や typed initialization algorithm の correctness は主張しない。

## Concrete controls / destructive validation

既存 `Counterexample/Transition.lean` の reviewed private finite tree を再利用し、`FieldLifecycle` section に25 public controlsを追加する。tree の8 tracked places、depth-2 `x`、sibling `y`、opaque local fragments は既存のまま。production namespace に broken acquisition rule を入れない。

| Control family | machine-checked result |
| --- | --- |
| live nested field / wrong identity | positive acquisition; wrong path/incarnation/root/site/sibling/domain reject |
| omitted acquisition premises | current token alone does not supply stability/access; omitted liveness accepts inactive data but actual acquisition rejects |
| Change / acquisition | old current fact dies, same token acquires with fresh post evidence; missing evidence rejects; sibling does not retarget |
| semantic dependency blocker | acquired field ref does not allow returned-old-value dependency laundering |
| take / destroy | independent root take/destroy legal; same stored fact with dead child incarnation cannot acquire |
| authority | field access does not supply parent ending authority; take needs read; destroy does not inherit take-read |
| old-only dependency | old child dependency rejects take but is atomically consumed by discardable destroy |
| unchecked take | raw candidate carries exact ended dependency and fails post WF; survivor guard is necessary |
| external survivor | loose package depending on ended child fact rejects both take and destroy |
| non-Discardable root | take can be legal; destroy rejects independently of dependency safety |
| restart | fresh same-site tree WF, new token acquires, old token rejects; history reuse rejects |
| composed lifecycle | the same token survives actual leaf Change, then becomes unusable after legal parent take/destroy |

General rejection lemmas also cover an external installed root's local dependent fragment, not only the concrete loose-survivor fixture. The guard is exact surviving-carrier validation, not a special ptr prohibition.

## F-G — generalization boundary

| Direction | 今回で閉じる / 後続へ残すもの |
| --- | --- |
| nested fixed path | token は arbitrary finite path を持ち、depth-2 concrete witness と general layout/identity frame を証明する |
| ptr-valued field | content を non-pointer に制限しない。embedded token の encoding/decoding、typed source issuance、persistent provenance transfer は未証明 |
| optional ptr payload | conditional occurrence の既存 slice は変更しない。active occurrence guard を fixed-field predicateに自動追加せず、sum/fixed embedding adapter は後続 |
| recursive nominal field | finite tree に限る。recursive Node、dynamic allocation、recursive ownership algebra は未実装 |
| raw-backed fixed aggregate | caller access に backing obligations を残し、region/addressからauthorityを生成しない。full Placement/Storage/slot accountingとのfixed-tree adapterは未証明 |

この表の未証明 interface を「不可能」や新しい normative restriction と解釈しない。F1 Unknown-effect concretization の hook も本 adjunct では閉じない。

## FORMAL findings

- **FORMAL-ENCODING — resolved within bound**: root-only pointer erasureでは field designation を保持できなかった。独立した field token/current-target/acquisition relation を追加し、F0 public interface は変更しない。
- **FORMAL-ENCODING — resolved within bound**: rich fixed-tree EndRoot と descendant-token rejection の hook は、既存 live-root support を除去する minimal adapter で表現できた。fresh-tree restart は全 node freshness certificate と concrete WF witness まで。full fixed-tree initialize / geometry adapterを証明したとは扱わない。
- **FORMAL-LEMMA**: Change preservation、exact root/descendant end、derived post invariants、take/destroy survivor差、same-site historical non-revivalを47 general declarationsと25 controlsでmachine-checkした。
- **FORMAL-SCOPE**: source ref derivation/future-use、ptr payload decoding、conditional embedding、Unknown effect adapter、raw-backed full composition、recursive Node、allocator、F3.1は後続。root termination の exact domain/ending permissionとaccess/stabilityの導出はcaller obligations。
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION**: bounded comparisonで発見なし。canonicalの規則を追加・変更しない。

## Verification / review handoff

- 変更前の main: `lake build` PASS、`bash scripts/check-proofs.sh` **1007 PASS**。
- branch: `lake build` PASS、proof audit **1079 declarations**（既存1007を順序どおり保持、47 general + 25 controlsを追加）。全追加public theoremをauditする。
- project-owned Lean source の proof placeholderは禁止。許可axiom dependencyは従来どおり `propext` / `Classical.choice` / `Quot.sound` のみ。
- Lean `v4.34.1`、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、manifest、bootstrap、CI workflowは不変。
- exact final head / PR-event `Lean proofs` run / remote結果はIssue #31の `Track: F` handbackとPR本文へ記録する。local PASSをremote CI PASSとして扱わない。
- PRとIssueはCoordination review用にOPEN、PRはunmergedのまま残す。

No source syntax、compiler/field P implementation、recursive Node、allocator/raw-storage implementation、cJSON、F3.1、canonical Draft edit。本adjunct以降の実装に進まない。

Review handoff marker（exact-head CI確認後）: **F FIELD-PTR LIFECYCLE ADAPTER READY FOR REVIEW**。

## Audited theorem inventory

以下の全72件を既存auditに追加する。private fixture helpersはpublic inventoryに含めないが、通常のLean kernel buildで検査する。

### `NewLang.F1.Reference` — 20 declarations

Source: [NewLang/F1/Reference.lean](../NewLang/F1/Reference.lean)

- `token_at_live_field_is_current`
- `acquire_requires_current_target`
- `acquire_implies_live_child_incarnation`
- `acquire_implies_live_parent_incarnation`
- `acquire_implies_live_governing_domain`
- `acquire_does_not_mint_access`
- `acquire_rejects_missing_stability`
- `acquire_rejects_missing_access`
- `acquire_rejects_wrong_path`
- `acquire_rejects_wrong_incarnation`
- `acquire_rejects_wrong_root_place`
- `acquire_rejects_wrong_root_incarnation`
- `acquire_rejects_wrong_domain`
- `acquire_rejects_wrong_site`
- `acquire_rejects_retargeted_field`
- `current_token_can_acquire`
- `field_replace_preserves_current_token`
- `field_replace_reacquires_with_post_evidence`
- `field_replace_preserves_token_at`
- `acquisition_does_not_bypass_current_dependency`

### `NewLang.F1.FixedLifetime` — 27 declarations

Source: [NewLang/F1/FixedLifetime.lean](../NewLang/F1/FixedLifetime.lean)

- `end_live_node_iff`
- `end_candidate_wellFormed`
- `end_preserves_wellFormed`
- `end_ends_every_fixed_incarnation`
- `end_ends_every_fixed_current_fact`
- `end_rejects_old_field_acquisition`
- `end_retains_identity_history`
- `ended_field_token_remains_recorded`
- `fresh_tree_restart_rejects_recorded_field_token`
- `end_then_fresh_restart_rejects_old_field_token`
- `end_rejects_missing_authority`
- `take_requires_ordinary_read`
- `destroy_requires_discardability`
- `end_preserves_other_node_identity`
- `end_preserves_domains`
- `take_returns_exact_value`
- `destroy_does_not_return_old_value`
- `take_has_f0_root_shadow`
- `destroy_has_f0_root_shadow`
- `take_root_occupancy_commutes_with_erasure`
- `destroy_root_occupancy_commutes_with_erasure`
- `take_parent_incarnation_ends_in_erasure`
- `destroy_parent_incarnation_ends_in_erasure`
- `take_rejects_returned_ended_fact_dependency`
- `end_rejects_external_ended_fact_dependency`
- `end_rejects_loose_ended_fact_dependency`
- `acquisition_does_not_mint_ending_authority`

### `NewLang.F1.Counterexample.Transition` — 25 declarations

Source: [NewLang/F1/Counterexample/Transition.lean](../NewLang/F1/Counterexample/Transition.lean)

- `live_nested_field_can_acquire`
- `field_token_rejects_wrong_path`
- `field_token_rejects_wrong_incarnation`
- `field_token_rejects_wrong_parent_place`
- `field_token_rejects_wrong_parent_incarnation`
- `field_token_rejects_wrong_site`
- `field_token_rejects_retargeting_to_sibling`
- `field_token_rejects_wrong_domain`
- `current_field_token_does_not_supply_stability_or_access`
- `omitting_liveness_accepts_inactive_root_table_data`
- `field_change_kills_value_fact_but_preserves_acquisition`
- `field_change_still_requires_new_acquisition_evidence`
- `sibling_change_does_not_retarget_field_token`
- `acquired_field_ref_cannot_launder_old_value_dependency`
- `independent_parent_take_and_destroy_are_legal`
- `parent_end_stales_field_token_without_changing_stored_fact`
- `field_access_does_not_grant_parent_ending_authority`
- `old_child_dependency_rejects_take_but_allows_destroy`
- `unchecked_take_preserves_dead_dependency_in_returned_value`
- `external_loose_dependency_rejects_both_parent_end_modes`
- `nondiscardable_root_can_be_taken_but_not_destroyed`
- `destroy_does_not_inherit_take_read_requirement`
- `fresh_same_site_tree_restart_does_not_revive_old_field_token`
- `historical_child_id_reuse_cannot_satisfy_restart_certificate`
- `same_field_token_survives_change_then_stales_after_parent_end`
