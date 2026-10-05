# F1.4 — Raw occupancy / Storage / slot責任保存

[English](F1_4_RAW_OCCUPANCY_REPORT.md)

**F1.4 REVIEWED / MERGED / CLOSED**。proof reportであり、normative文書ではありません。変更履歴の正はGitで、独自Version historyは持ちません。

## 運用・正本・baseline

最初にCompiler mainの[NewLang_Project_Development_Process.md](https://github.com/wakairo/NewLang_Compiler/blob/d4eff722fc7ee1a609875b51dcecbbf953dfe737/docs/NewLang_Project_Development_Process.md)を確認しました。substantiveな[Issue #13](https://github.com/wakairo/NewLang_FormalProof/issues/13) commentには**Track: F**を明記します。

Compiler mainは`d4eff722fc7ee1a609875b51dcecbbf953dfe737`、CURRENT_SPECは**Draft 17.8**。確認範囲は§3.3–3.5 / §14.1–3 / §23.1です。古いP4文書のempty/endpoint ambiguityを引き継ぎません。FormalProof main/baseは`1446011d7a9fa1b16fcb0cbbe88b660a57d28f2d`、F1.3はreview・merge済み/CLOSEDでした。変更前に`lake build` PASS、proof audit **639件PASS**を確認しました。

実装branchはPR #14でreviewされmainへmerge済みです。このmerge自体ではF1.5/P5/M9/Sync/Red Teamを開始していません。historical local Draft 17.4も変更していません。

## State/modelとclaim境界

`Range(base,length)`はregion-relativeな半開区間です。`Extent`は既存F1.3 BackingRegionIdを加えます。Geometryはrelative ordinalを既存abstract byteへinjectiveに写し、World.bytesと整合させます。numeric machine addressからidentity/authorityを得るmodelではありません。独立live regionのRegionsDisjointを維持します。

`Layout`はstatic type key→positive sizeofのproof contextです。Draft 17.8 §23.1のstorable Tに対応し、into_slotは**length = sizeof(T)**を要求します。alignment、typed/representation validity、platform ending applicabilityはcaller obligationです。ABI arithmeticやfrontend derivationは実装しません。

proof-only finite Ledgerは明示region scope、active ClaimId handle、inactiveな記録を持ちます。inactive recordにはauthorityがありません。

- `storage e`: value-owned raw responsibility、affine/non-Copy/non-Discardable。
- `slot t e`: value-owned definitely-empty typed responsibility、semantic T valueを持たない。
- `root t location e`: state-owned live placementと**同じ責任のaccounting view**。第二ownerではない。

ClaimIdはcurrent ghost handleで、inactive IDの再利用を許します。historical object identityのfreshnessとは別です。既存incarnation/value/occurrence historyとstale規則は変更しません。runtime counter/ledger/shadow bitmap/source-visible ownerを要求しません。**Formal representation choices are non-normative.**

AccountingShapeはgeometry一致、region separation、scope liveness、claim-in-scope、positive length、range fit、static exact typed size、live-root対応、exact placement対応を持ちます。AccountingはNoOverlapと**明示scoped regionのcomplete exact coverage**を追加します。scope外のlive regionは許し、allocator全体のowner algebraにはしません。各modeled byteにactiveな責任handleがちょうど一つ存在します。raw/empty/liveすべてでlive backingを要求します。fixed ancestor/descendantへ独立責任の非overlap条件を広げません。

## Operationと主要結果

splitは`0 < k < n`でsourceをatomicに消費し、同じregionのnonempty/disjoint/exactな二片を作ります。mergeはdistinctなnonempty・same-region・adjacent raw carrierをatomicに消費し、逆順も許してcontiguous exact unionへ戻します。**全ledger footprint**とframed claimに対するNoOverlapを保存します。immediate split→mergeの両順序witnessもあります。

into_slotはexact-size raw carrierを同一extentのempty typed claimへ変換し、暗黙tail splitを行いません。erase_slotは同一extentのStorageへ変換し、read/write条件なしでsafe/totalです。両conversionはpre AccountとRawからpost Accountを導出します。

lifecycle wrapperは既存F1.3 RawInitialize/RawTake/RawDestroyを直接使います。initializeは供給slotを消費し同じregion/rangeでrootを開始します。takeは同じempty責任を返し、semantic Tにsource placementを所有させません。destroyも同じempty責任を返します。既存Discardable/ending条件を保ち、initialize write、take ptr/backing read、destroyはtake-readを継承しない規則を確認します。root終了だけではbacking/scopeを終了しません。同じrangeのfresh restart後も旧ptrはstaleです。

split/merge/lifecycleのlegal stepは既存**Raw candidate + pre/post invariant**方針を維持します。任意raw lifecycle candidateのsemantic合法性は仮定しません。conservation/global no-overlapを別に証明し、合法endpointの具体例でvacuityを除きます。caller/static条件やgeneric transition frameworkの証明ではありません。

4-byte regionを二分し、左半分をinto_slot→initialize→take→同一rangeのfresh initialize→destroy→erase_slotへ進めます。右半分はraw claimのまま保持し、最後に一つのfull Storageへmergeします。source carrierの消費、exact責任、root historyを確認します。WO initialize/destroy合法・WO take拒否も別witnessで検証します。fixtureのlayout/ID選択はnormative runtime要求ではありません。

## Erasure・representation frame

flat WellFormedは既存9 semantic fieldを明示継承します。PhysicalWellFormedはAccountingから**導出**し、erased WellFormedを隠れた仮定にしません。erasureはledger/relative-range/layout precisionをforgetしてexactなF1.3 flat stateとF0義務を保持します。conditional productも既存F1.2 Invariantと単一DependenciesValidを明示継承し、backingを導いて既存F1.3→F1.2→F1.1→F0 proofへ接続します。sum lifetime start/end、任意typed embedding、exact Step simulationは主張しません。

representation-only mutationはopaque contents markerと**authority frame**だけです。marker変更の具体例でsemantic/physical/claim authority stateが全て保存されます。per-byte validityやstorage_read/write/copy operation、frontend ptr minting、任意unsafe raw operationの安全性は実装・証明しません。

## 必須isolated control対応

controlはproduction外の`NewLang.F1.Occupancy.Counterexample`に分離します。wrong-rangeのwell-formed endpointではcomplementary raw halfも再配置していますが、exact candidate/frame relationに従わないため拒否します。overlapは定義上well-formed merge sourceにはできないため、shape/coverageを保持し独立no-overlap違反も明示します。下表の英語result欄は検証した失敗境界を具体的に示します。

| Issue control | Rule | Audited declaration(s) | Isolation / result |
| --- | --- | --- | --- |
| 1 | Endpoint split / empty Storage | `endpoint_split_controls` | Valid raw source; both endpoint results have length 0; RawSplit rejects. |
| 2 | Split gap / lost byte | `gap_split_isolates_lost_responsibility` | All AccountingShape and NoOverlap hold; byte 1 loses coverage. |
| 3 | Split overlap / duplicate byte | `overlapping_split_isolates_duplication` | All shape and exact coverage hold; byte 2 breaks only NoOverlap. |
| 4 | Different-region merge | `different_region_merge_isolates_identity` | Complete valid two-region source with nonempty relatively adjacent inputs; nominal identity guard rejects. |
| 5 | Merge gap / overlap | `merge_gap_and_overlap_controls` | Gap source is fully accounted, with a third raw carrier filling the gap; gap/overlap are nonadjacent. Overlap intentionally breaks pre disjointness too. |
| 6 | Larger into_slot / dropped tail | `larger_into_slot_tail_control`; `unchecked_into_slot_loses_tail` | Valid source and exact-size endpoints; larger input rejects. Private tail-drop candidate retains shape/NoOverlap and loses only coverage, at byte 2. |
| 7 | Storage + slot duplicate | `storage_and_slot_overlap_isolated` | Semantic validity, all shape and coverage remain; only NoOverlap fails. |
| 8 | Slot + live-root duplicate | `slot_and_live_root_overlap_isolated` | Semantic validity, all shape and coverage remain; only NoOverlap fails. |
| 9 | Initialize at wrong range | `initialize_wrong_range_control_has_valid_endpoints` | Both states are fully well formed and the semantic post matches; wrong placement violates raw exact-destination relation. |
| 10 | Take returns wrong slot range | `take_wrong_slot_control_has_valid_endpoints` | Both states are fully well formed, including exact reviewed flat take post; ledger frame/exact-slot relation rejects. |
| 11 | Destroy loses responsibility | `destroy_lost_responsibility_control` | Semantic validity, shape and NoOverlap remain; left bytes lose coverage and required returned slot is absent. |
| 12 | Erase_slot mints wrong/larger Storage | `erase_slot_wrong_range_control_has_valid_endpoints`; `erase_slot_larger_or_different_region_controls` | Wrong-range case has fully valid endpoints; independent larger/different nominal region controls reject exact conversion. |
| 13 | Reconstruct full Storage with outstanding subclaim | `outstanding_slot_blocks_full_storage`; `outstanding_root_blocks_full_storage` | All shape/coverage remain; independent full Storage duplicates slot/root responsibility. Universal full_region_storage_excludes_outstanding_subclaim also covers raw subclaims. |

## FORMAL findings・scope exclusions

- **FORMAL-ENCODING:** relative interval/geometry、ghost handle、明示scopeのcoverage、root placementの同一責任accountingはproof representationで、runtime metadataや第二physical identity modelではありません。
- **FORMAL-LEMMA:** exact footprint conservationとglobal disjointnessでloss/duplicationを防ぎます。live-backed unique responsibility、total erase conversion、既存access/stale ruleを別にmachine-checkします。
- **FORMAL-EXTRACTION — 解決済みreport解釈:** 旧F1.3 reportのempty extent→zero-sized rootという説明を訂正します。Draft 17.8 §23.1は全storable typeで`sizeof(T) >= 1`を要求します。最小witnessはtyped exact-size proofのないF1.3 empty Placementで、これだけではzero-sized storable objectを証明できません。旧reportをlimited untyped encodingと明記し、正本・F1.3コード・public theorem・whitelistは変更しません。F1.4でpositive exact-size responsibilityをconservatively追加します。
- **FORMAL-HOLE / FORMAL-AMBIGUITY:** 確認したcanonical範囲では**なし**。未解決canonical extractionもなくCoordinator判断は不要です。endpoint/nonempty/exact-size規則は明示されています。
- **FORMAL-SCOPE:** Allocation/deallocator/allocator failure、relocation、numeric pointer authority、general dynamic-container owner、parent/child非overlap、FFI/MMIO/volatile、frontend/P5/M9/Sync、per-byte Defined、mandatory shadow bitmap、full raw-byte operationは含めません。

## Build・audit・CI・review handoff

Lean/Lakeは`leanprover/lean4:v4.34.1`（release `5045d0056413266e57c625dcd7c365b10e377c52`）、elan 4.2.4、mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`のままです。toolchain/manifest/bootstrap/workflowは変更しません。

local `lake build`と`bash scripts/check-proofs.sh`はPASS。既存639 audited declarationを元の順序で全て保持し、public theorem **118件**（production/helper **76**、validation/helper **42**）を追加して合計**757件**です。project-owned Lean sourceに禁止placeholderやcustom semantic仮定はありません。許可logicは従来の`propext` / `Classical.choice` / `Quot.sound`のみです。private supportもaudit対象proofの依存としてkernel-checkされます。

既存`Lean proofs`はpush/pull_requestでpinned環境をbootstrapします。**final headと一致するpull_request run/jobのURL・success・PR number・head SHA**は[Issue #13のTrack: F READY FOR REVIEW handoff](https://github.com/wakairo/NewLang_FormalProof/issues/13)をreview-head CI evidenceとします。self-referential commit/version logはreport内へ複製しません。そのcheck成功後にのみREADYを公開し、その後PR #14はreview・mergeされました。

## 追加auditのexact theorem inventory

以下が全118件です。generated projection/private supportは個別countに含めません。全て既存standard-logic policyで検査します。

### [NewLang/F1/Occupancy/Claims.lean](../NewLang/F1/Occupancy/Claims.lean) — 21

Namespace: `NewLang.F1.Occupancy`.

- `consumeOne_active_iff`
- `consumeOne_consumes_source`
- `consumeOne_produces_result`
- `consumeOne_conserves_footprint`
- `split_consumes_source_and_produces_two`
- `split_preserves_identity_nonempty_partition`
- `split_rejects_left_endpoint`
- `split_rejects_right_endpoint`
- `split_conserves_all_byte_responsibility`
- `split_preserves_scope`
- `merge_consumes_both_inputs`
- `merge_preserves_identity_and_exact_union`
- `merge_rejects_different_regions`
- `merge_rejects_nonadjacent`
- `merge_conserves_all_byte_responsibility`
- `into_slot_consumes_raw_exact_range`
- `into_slot_rejects_larger_range`
- `into_slot_conserves_all_byte_responsibility`
- `erase_slot_consumes_empty_exact_range`
- `erase_slot_conserves_all_byte_responsibility`
- `erase_slot_has_no_access_precondition`

### [NewLang/F1/Occupancy/Conversion.lean](../NewLang/F1/Occupancy/Conversion.lean) — 6

Namespace: `NewLang.F1.Occupancy`.

- `empty_conversion_preserves_accounting`
- `into_slot_step_of_raw`
- `erase_slot_step_of_raw`
- `erase_slot_is_total`
- `empty_claim_conversion_preserves_flat`
- `empty_claim_conversion_preserves_sum`

### [NewLang/F1/Occupancy/Counterexample/Claims.lean](../NewLang/F1/Occupancy/Counterexample/Claims.lean) — 9

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `endpoint_split_controls`
- `gap_split_isolates_lost_responsibility`
- `overlapping_split_isolates_duplication`
- `merge_gap_and_overlap_controls`
- `different_region_merge_isolates_identity`
- `different_region_merge_control`
- `larger_into_slot_tail_control`
- `unchecked_into_slot_loses_tail`
- `split_merge_roundtrip_is_legal`

### [NewLang/F1/Occupancy/Counterexample/Cycle.lean](../NewLang/F1/Occupancy/Counterexample/Cycle.lean) — 19

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `single_raw_accounting`
- `raw_state_wellFormed`
- `split_is_legal`
- `slot_state_wellFormed`
- `into_slot_is_legal`
- `first_wellFormed`
- `taken_wellFormed`
- `restart_wellFormed`
- `ended_wellFormed`
- `initialize_is_legal`
- `take_is_legal`
- `same_range_restart_is_legal_and_old_ptr_stays_stale`
- `destroy_is_legal`
- `erase_slot_is_legal`
- `merged_wellFormed`
- `merge_after_lifecycle_is_legal`
- `writeonly_destroy_is_legal`
- `writeonly_take_rejected_but_destroy_allowed`
- `complete_responsibility_cycle`

### [NewLang/F1/Occupancy/Counterexample/Fixtures.lean](../NewLang/F1/Occupancy/Counterexample/Fixtures.lean) — 4

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `live_iff`
- `semantic_wf`
- `pair_shape`
- `pair_accounting`

### [NewLang/F1/Occupancy/Counterexample/Lifetime.lean](../NewLang/F1/Occupancy/Counterexample/Lifetime.lean) — 6

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `initialize_wrong_range_control_has_valid_endpoints`
- `take_wrong_slot_control_has_valid_endpoints`
- `erase_slot_wrong_range_control_has_valid_endpoints`
- `destroy_lost_responsibility_control`
- `erase_slot_larger_or_different_region_controls`
- `representation_change_is_possible_without_new_authority`

### [NewLang/F1/Occupancy/Counterexample/Overlap.lean](../NewLang/F1/Occupancy/Counterexample/Overlap.lean) — 4

Namespace: `NewLang.F1.Occupancy.Counterexample`.

- `storage_and_slot_overlap_isolated`
- `slot_and_live_root_overlap_isolated`
- `outstanding_slot_blocks_full_storage`
- `outstanding_root_blocks_full_storage`

### [NewLang/F1/Occupancy/Lifetime.lean](../NewLang/F1/Occupancy/Lifetime.lean) — 19

Namespace: `NewLang.F1.Occupancy`.

- `initialize_consumes_slot_and_preserves_exact_responsibility`
- `initialize_conserves_byte_responsibility`
- `initialize_preserves_backing_lifetime_and_scope`
- `initialize_requires_reviewed_write_access`
- `initialize_rejects_readonly_backing`
- `initialize_step_erases_to_backing`
- `take_consumes_root_and_returns_same_slot`
- `destroy_consumes_root_and_returns_same_slot`
- `take_conserves_byte_responsibility`
- `destroy_conserves_byte_responsibility`
- `take_does_not_end_backing`
- `destroy_does_not_end_backing`
- `take_transfers_value_without_placement`
- `take_requires_reviewed_read_access`
- `take_rejects_writeonly_ptr`
- `take_step_erases_to_backing`
- `destroy_step_erases_to_backing`
- `take_then_same_range_restart_rejects_stale_ptr`
- `representation_mutation_cannot_mint_authority`

### [NewLang/F1/Occupancy/Model.lean](../NewLang/F1/Occupancy/Model.lean) — 13

Namespace: `NewLang.F1.Occupancy`.

- `accounting_derives_physical_wellFormed`
- `wellFormed_erases_to_backing`
- `wellFormed_erases_to_f0`
- `sum_wellFormed_erases_to_backing`
- `sum_wellFormed_erases_to_conditional`
- `sum_wellFormed_erases_to_current`
- `sum_wellFormed_erases_to_f0`
- `surviving_claim_requires_live_backing`
- `every_scoped_byte_has_unique_responsibility`
- `nonempty_claim_cannot_be_covered_twice`
- `full_region_storage_excludes_outstanding_subclaim`
- `storage_is_affine_nonDiscardable`
- `slot_is_empty_authority_not_live_value`

### [NewLang/F1/Occupancy/Partition.lean](../NewLang/F1/Occupancy/Partition.lean) — 2

Namespace: `NewLang.F1.Occupancy`.

- `split_preserves_no_overlap`
- `merge_preserves_no_overlap`

### [NewLang/F1/Occupancy/Range.lean](../NewLang/F1/Occupancy/Range.lean) — 15

Namespace: `NewLang.F1.Occupancy`.

- `range_membership`
- `nonempty_range_has_position`
- `split_ranges_are_nonempty`
- `split_ranges_exact_union`
- `split_ranges_disjoint`
- `split_extents_preserve_region`
- `split_extents_exact_union`
- `split_extents_disjoint`
- `adjacent_ranges_disjoint`
- `adjacent_ranges_exact_union`
- `adjacent_extents_exact_union`
- `adjacent_extents_disjoint`
- `split_merge_range_roundtrip`
- `extent_footprint_nonempty`
- `fitting_extent_is_inside_backing`
