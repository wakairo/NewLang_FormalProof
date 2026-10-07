# F3.0-pre — occurrence-aware rich sum lifetime adapter pilot

Track: F

**F3.0-PRE READY FOR REVIEW**。これは Issue [#23](https://github.com/wakairo/NewLang_FormalProof/issues/23) の bounded prerequisite であり、global Safe Core theorem ではない。F3.0 [#22](https://github.com/wakairo/NewLang_FormalProof/issues/22) の BLOCKED disposition は、この pilot の review/merge と Coordination の再裁定まで維持する。変更履歴は Git を正とする。

## Authority と baseline

最初に Compiler main の `docs/NewLang_Project_Development_Process.md` を確認した。作業開始時の main は両 repository とも指定 SHA に一致した。

- Compiler main: `eda75ad09a73cacd0a78d1a0496aa0a86bd77a32`。
- `docs/reference/CURRENT_SPEC.md`: **Draft 17.17**。
- FormalProof base main: `e591e53f295d4ab76d00d3bc1a2cdc443e06b7b4`。
- F0–F2: CLOSED。F3.0 #22: BLOCKED — MISSING FORMAL INTERFACE。
- baseline `lake build`: PASS、770 jobs。baseline proof audit: PASS、930 declarations。
- Lean `leanprover/lean4:v4.34.1`、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`、manifest/bootstrap/workflow は変更していない。

normative source は Compiler CURRENT_SPEC が指す Draft。local Draft 17.4 は historical snapshot。新しい Lean representation は non-normative。

## Authoritative state と正確な bound

既存 `Occupancy.SumState` をそのまま使用する。semantic authority は `base.semantic : Conditional.State`、physical state は `base.physical`、responsibility は既存 `Ledger`。F1.2 / F1.4 public definitions と statements を変更していない。

`EndingInput` は明示的に次を要求する:

```text
semantic.liveRoots = {sourceLocation}
ledger.scope = {extent.region}
ledger.active = {sourceClaim}
Has ledger sourceClaim (root type sourceLocation extent)
resultClaim is inactive
ending domain = source governing domain
exact current root token + valid backing/access evidence
explicit caller ending/representation authority ce
```

external loose semantic packages は任意に存在できる。ただし、別の live typed root、別の active raw claim、arbitrary fixed/nested layout はこの pilot に入らない。configured `Layout` の type size、positive length、fit、region geometry、coverage は pre accounting で検査され、同 extent の slot へ運ばれる。`ce` は既存 F0/F1.3 と同じ explicit caller authority / omitted provenance-representation obligation の境界であり、post safety 全体を意味しない。exclusive-ref derivation 全体はここで新設しない。

## Atomic take / destroy

`endCandidate` は one-root premise の下で root carrier を終了する。inactive root record は inert な table data として残す。liveness を与える `liveRoots` は空、source placement は終了、他の placement は frame する。

| State component | take | destroy |
|---|---|---|
| root incarnation / current fact | live でなくなる | live でなくなる |
| active occurrence / payload fact | live でなくなる | live でなくなる |
| old semantic package | loose result として survive | surviving carrier がなくなる |
| values/dependency/type data | 完全に unchanged | table data は残せるが carrier は消費 |
| loose external survivors | unchanged | unchanged |
| domain / backing world | unchanged、ending root だけでは終了しない | 同左 |
| historical identities | 全 sets unchanged | 同左 |
| responsibility | root claim -> exact same-type/same-extent slot | 同左 |

take は ptr/backing read を要求し、non-Discardable sum でも合法 witness がある。destroy は sum type 全体の static `SemanticValue.discardable` を要求する。current variant だけから capability を計算しない。destroy は returned T を作らないため take の read guard を継承しない。write-only backing での legal destroy witness を含む。

この transition は source 側の consume-out / lifetime-end adapter である。ordinary source call/return/lexical destination start を形式化したものではない。

## Survivor guard と非自明な保存証明

`Ended(root, fact)` は exact root current fact、optional occurrence、optional payload fact を列挙する。domain facts はこの operation では終了しない。persistent provenance を自動的に blocker として追加しない。

`SurvivorGuard(pre, location, returned)` は actual package data を使う local conflict check:

```text
for each package in remainingCarriers(pre):
    for each dependency in its unchanged value:
        dependency is not an Ended fact
```

take の remaining carriers は `insert oldPackage pre.loosePackages`、destroy は `erase oldPackage pre.loosePackages`。guard は post WellFormed / post DependenciesValid の別名ではない。pre の carrier・value・fact を有限に検査し、終了factとの exact conflict だけを述べる。

legal Step の入力は **pre SumWellFormed + Raw operation + SurvivorGuard**。post WellFormed は定義にも theorem premise にも入れない。

proof chain:

```text
pre SumWellFormed
  -> every remaining package previously survived
  -> each actual dependency was pre-live
single live root + not Ended
  -> dependency remains post-live
  -> post DependenciesValid

pre structural/type/carrier invariant
  -> candidate structural/type/carrier invariant

pre exact accounting + single root/claim bound + same extent conversion
  -> post accounting, coverage, NoOverlap, unique byte responsibility

all three
  -> post SumWellFormed
```

`take_preserves_wellFormed` / `destroy_preserves_wellFormed` はこの chain の結論。F0/F1 の projection-style preservation theorem を結論として呼ぶだけの proof ではない。

## Responsibility と histories

既存 `consumeOne` を再利用し、source claim をconsume、inactive result handleへ `.slot t e` を生成する。handle は ghost responsibility carrier であり historical object identity ではない。

`end_accounting` は geometry、live scope、positive/fitting/typed extent、root/placement exactness、coverage、NoOverlap を個別に導く。`end_responsibility` と `end_footprint_conserved` は source の消費、unique result、same region/extent、scope/backing保持、byte unionの完全保存を証明する。既存 unique-byte theorem を適用できる full `Accounting` が得られる。missing/duplicate responsibility と wrong region/extent の controls がある。

`end_preserves_value_and_history` は table と `usedValueFacts` / `usedIncarnations` / `usedOccurrences` 全体の equality を証明する。ended identity と retired ID 9 を保持する具体例もある。runtime bitmap/history counter を要求しない。

## Erasure / refinement direction

`coarse` は one-root adapter用の ordinary F0 view。exact root fields / carriers / history と `Conditional.projectFacts` を使用する。F1.1 fixed-layout の中間表現を経由する state erasure とは区別し、両者の一般的 literal equality は主張しない。

- `coarse_wellFormed` は rich WellFormed -> ordinary-view WellFormed を証明する。
- `raw_take_projects` / `raw_destroy_projects` は実際の既存 F1.4 raw lifetime relation へ同じ physical/ledger candidate を射影する。
- `rich_take_projects_to_legal_coarse` / `rich_destroy_projects_to_legal_coarse` は合法 rich Step -> 合法 coarse F1.4 Step。coarse post WF は新規 rich preservation proof から導く。
- `rich_take_reviewed_erasure_wellFormed` / `rich_destroy_reviewed_erasure_wellFormed` は、既存 `Conditional.erase -> F1.eraseToF0` chain の post invariant sanity も保つ。

逆向きの legality は不可。`coarse_legal_take_does_not_imply_rich_legal_take` は well-formed rich pre、legal coarse F1.4 take、rich take rejection を一つの concrete witness で証明する。old sum package は payload dependency `{Occurrence(old)}` を持つ。projection はそれを消すので coarse take は成立するが、rich result は unchanged dependency を持ったまま survive し、old occurrence は dead なので拒否される。

さらに `raw_candidate_has_structure_and_accounting_but_bad_dependencies` は同じ candidate の **Conditional.Invariant と Accounting は成立、DependenciesValid だけが不成立**を証明する。従って今回の reject は ad-hoc sum prohibition でも、不正 physical endpoint による偶然でもない。

## Canonical clause mapping

| Draft 17.17 rule | Adapter / proof |
|---|---|
| §3.3–3.6 Storage/slot/live-root responsibility | existing Ledger/Accounting、root -> exact slot、coverage/NoOverlap |
| backing/placement/access clauses、§14.2 source read | current exact AccessPtr、EvidenceValid、read non-amplification、placement end/backing frame |
| §13.5a surviving-dependency rule | exact `Ended` + `SurvivorGuard`、take vs destroy、external survivor rejection |
| §14.2 take | root end、returned semantic value unchanged、same empty responsibility、read/ending requirement |
| §14.3 destroy | single atomic end/discard、static Discardable、no inherited take-read requirement |
| §18.6 consume-out | source identity/domain/placement relation does not travel with value。source side only、destination binding/call は未実装 |
| §26.6 conditional payload occurrence | enclosing root終了に従い occurrence/payload factも終了 |
| §26.7 value / occurrence non-transfer | value data unchanged、old occurrenceはresultへtransferせずdead、dependencyはretargetしない |

## Required controls / positive witnesses

| Requirement | Declaration（namespace `Counterexample`） |
|---|---|
| independent non-Discardable take | `independent_rich_take_is_legal` |
| valid endpoint / unique loose / exact slot footprint | `take_positive_endpoint_and_exact_responsibility` |
| root/occurrence/payload facts end | `occurrence_payload_root_facts_end` |
| unchanged dependencies / ended and retired histories | `dependency_data_and_retired_history_preserved` |
| external survivor / still-live ordinary fixed domain fact | `external_and_fixed_domain_dependency_remain_valid` |
| returned occurrence dependency rejects | `returned_occurrence_dependency_rejects_take` |
| returned payload dependency rejects | `returned_payload_dependency_rejects_take` |
| returned root current dependency rejects | `returned_root_fact_dependency_rejects_take` |
| old-only occurrence dependency consumed by WO destroy | `destroy_can_consume_old_only_occurrence_dependency` |
| same pre-state take-vs-destroy contrast | `old_occurrence_dependency_rejects_take_but_allows_destroy` |
| external occurrence dependency rejects both | `external_occurrence_dependency_rejects_take_and_destroy` |
| coarse legal / rich illegal anti-lifting witness | `coarse_legal_take_does_not_imply_rich_legal_take` |
| all non-dependency invariant fields pass broken raw candidate | `raw_candidate_has_structure_and_accounting_but_bad_dependencies` |
| stale token after take and destroy | `stale_root_token_rejected_after_both_endings` |
| missing read / ending authority | `take_rejects_missing_read_or_ending` |
| missing Discardable / ending authority | `destroy_rejects_missing_discard_or_ending` |
| wrong region / extent claim | `wrong_region_extent_conversion_rejected` |
| missing byte responsibility | `missing_responsibility_rejected` |
| duplicated byte responsibility | `duplicated_responsibility_rejected` |

**Forbidden design:** Raw + unconstrained post WellFormed -> legal Step。今回の definition には post invariant field がない。bad raw candidate controlにより、pre WF + raw だけでも不十分なことを確認した。

## Findings と F3.0 handback

- **FORMAL-INTERFACE-GAP:** #22 の occurrence-aware source lifetime seam を、この one-root pilot の範囲で埋めた。#22 の再開/解除は review/merge 後に Coordination が裁定する。
- **FORMAL-ENCODING:** finite ghost histories、inactive table records、single-claim responsibility、ordinary coarse view は non-normative。
- **FORMAL-SCOPE:** rich sum initialize、multiple live roots、nested/fixed layouts、function/control/F2 adapters、persistent ref future-use、production refinement は未実装。
- **FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION:** 新規 finding なし。canonical を変更していない。

F3.0がreview後に再利用できるのは bounded authoritative rich take/destroy、explicit survivor guardからの保存、exact responsibility conversion、one-way projectionとnegative reverse-lifting witness。最初の subset は **rich sums already-live/preinitialized + existing flat initialize** として分離可能であり、この pilot はその source-ending slice を支える。rich sum initialize は later extension interface として明記する必要がある。この bound を arbitrary sums/layouts に拡張したとはみなさない。

ordinary call/return、finite-control、F2 rich-memory adapter は別の contract work。global Safe Core soundness、production acceptance correctness、backend correctness はいずれも今回の結論ではない。F3.0 #22 を自動的に再開せず停止する。

## Verification / PR evidence

local `lake build` / `bash scripts/check-proofs.sh`: PASS。既存 **930** audited declarations を順序どおり維持し、**36 production/helper + 19 controls = 55** 追加、合計 **985**。全new public theoremをauditする。project-owned `sorry` / `axiom` / `admit` 使用なし、whitelist は `propext`, `Classical.choice`, `Quot.sound` から広げていない。

dedicated branch: `f3.0-pre-sum-lifetime`。PR は main 向け open/unmerged。exact head SHA、PR URL、`pull_request` event の **Lean proofs** run/job conclusion は [Issue #23](https://github.com/wakairo/NewLang_FormalProof/issues/23) の `Track: F` handoff に記録する。CIは既存 pinned workflowを使用する。Issue/PRをclose/mergeしない。

## Exact audited theorem inventory

以下は新規 public declarations の完全な一覧。private fixture support もこれらのproofを通じてkernel-checkされる。

```text
NewLang.F3.Memory.SumLifetime.coarse_live
NewLang.F3.Memory.SumLifetime.coarse_survives
NewLang.F3.Memory.SumLifetime.coarse_live_facts
NewLang.F3.Memory.SumLifetime.coarse_wellFormed
NewLang.F3.Memory.SumLifetime.remaining_was_surviving
NewLang.F3.Memory.SumLifetime.live_not_ended_remains_live
NewLang.F3.Memory.SumLifetime.end_semantic_invariant
NewLang.F3.Memory.SumLifetime.end_semantic_wellFormed
NewLang.F3.Memory.SumLifetime.end_all_facts_dead
NewLang.F3.Memory.SumLifetime.end_placement_empty
NewLang.F3.Memory.SumLifetime.end_accounting
NewLang.F3.Memory.SumLifetime.end_candidate_wellFormed
NewLang.F3.Memory.SumLifetime.take_preserves_wellFormed
NewLang.F3.Memory.SumLifetime.destroy_preserves_wellFormed
NewLang.F3.Memory.SumLifetime.end_preserves_value_and_history
NewLang.F3.Memory.SumLifetime.take_returns_unique_loose
NewLang.F3.Memory.SumLifetime.destroy_old_package_not_surviving
NewLang.F3.Memory.SumLifetime.end_responsibility
NewLang.F3.Memory.SumLifetime.end_footprint_conserved
NewLang.F3.Memory.SumLifetime.take_rejects_ended_dependency
NewLang.F3.Memory.SumLifetime.destroy_rejects_external_ended_dependency
NewLang.F3.Memory.SumLifetime.end_rejects_stale_root_token
NewLang.F3.Memory.SumLifetime.take_requires_read_and_ending
NewLang.F3.Memory.SumLifetime.destroy_requires_discard_and_ending
NewLang.F3.Memory.SumLifetime.raw_take_returns_exact_slot
NewLang.F3.Memory.SumLifetime.raw_destroy_returns_exact_slot
NewLang.F3.Memory.SumLifetime.end_frames_other_locations
NewLang.F3.Memory.SumLifetime.coarse_take_candidate
NewLang.F3.Memory.SumLifetime.coarse_destroy_candidate
NewLang.F3.Memory.SumLifetime.coarse_state_wellFormed
NewLang.F3.Memory.SumLifetime.raw_take_projects
NewLang.F3.Memory.SumLifetime.raw_destroy_projects
NewLang.F3.Memory.SumLifetime.rich_take_projects_to_legal_coarse
NewLang.F3.Memory.SumLifetime.rich_destroy_projects_to_legal_coarse
NewLang.F3.Memory.SumLifetime.rich_take_reviewed_erasure_wellFormed
NewLang.F3.Memory.SumLifetime.rich_destroy_reviewed_erasure_wellFormed
NewLang.F3.Memory.SumLifetime.Counterexample.independent_rich_take_is_legal
NewLang.F3.Memory.SumLifetime.Counterexample.take_positive_endpoint_and_exact_responsibility
NewLang.F3.Memory.SumLifetime.Counterexample.occurrence_payload_root_facts_end
NewLang.F3.Memory.SumLifetime.Counterexample.dependency_data_and_retired_history_preserved
NewLang.F3.Memory.SumLifetime.Counterexample.external_and_fixed_domain_dependency_remain_valid
NewLang.F3.Memory.SumLifetime.Counterexample.returned_occurrence_dependency_rejects_take
NewLang.F3.Memory.SumLifetime.Counterexample.returned_payload_dependency_rejects_take
NewLang.F3.Memory.SumLifetime.Counterexample.returned_root_fact_dependency_rejects_take
NewLang.F3.Memory.SumLifetime.Counterexample.destroy_can_consume_old_only_occurrence_dependency
NewLang.F3.Memory.SumLifetime.Counterexample.old_occurrence_dependency_rejects_take_but_allows_destroy
NewLang.F3.Memory.SumLifetime.Counterexample.external_occurrence_dependency_rejects_take_and_destroy
NewLang.F3.Memory.SumLifetime.Counterexample.coarse_legal_take_does_not_imply_rich_legal_take
NewLang.F3.Memory.SumLifetime.Counterexample.raw_candidate_has_structure_and_accounting_but_bad_dependencies
NewLang.F3.Memory.SumLifetime.Counterexample.stale_root_token_rejected_after_both_endings
NewLang.F3.Memory.SumLifetime.Counterexample.take_rejects_missing_read_or_ending
NewLang.F3.Memory.SumLifetime.Counterexample.destroy_rejects_missing_discard_or_ending
NewLang.F3.Memory.SumLifetime.Counterexample.wrong_region_extent_conversion_rejected
NewLang.F3.Memory.SumLifetime.Counterexample.missing_responsibility_rejected
NewLang.F3.Memory.SumLifetime.Counterexample.duplicated_responsibility_rejected
```
