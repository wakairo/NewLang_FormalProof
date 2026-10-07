# F adjunct — Stable-root replace / ptr lifecycle integration

Track: F

**F STABLE-ROOT INTEGRATION READY FOR REVIEW**

[FormalProof Issue #27](https://github.com/wakairo/NewLang_FormalProof/issues/27) の bounded integration task。既存 F0 state、Replace / Reference / Lifetime relation をそのまま使い、前後の取得と lifetime end を結合した。新しい model layer、language semantics、F3.1 実装は追加していない。変更履歴は Git を正とする。

## Authority と baseline

Compiler main の `docs/NewLang_Project_Development_Process.md` を最初に読み、substantive handback は `Track: F` として Issue #27 に記録する。作業開始時の current main は双方とも Issue の指定と一致した。

| Authority / check | Result |
| --- | --- |
| Compiler main | `355f1d2d1621cb5760b9dae7e9931753eedcc9f6` |
| `docs/reference/CURRENT_SPEC.md` | **Draft 17.19** |
| FormalProof main / base | `200afdada16eb2bf7bf0006aa7d41febc8bedffb` |
| baseline `lake build` | PASS、773 jobs |
| baseline proof audit | PASS、985 declarations |
| branch `lake build` | PASS、774 jobs |
| branch proof audit | PASS、992 declarations、standard logic only |
| project-owned placeholder scan | PASS、sorry / axiom / admit なし |
| Lean | `leanprover/lean4:v4.34.1`、変更なし |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612`、変更なし |

参照した canonical rule は §13.5a surviving dependencies、§13.7 local-derived ptr reacquisition / write-loan boundary、§14.2–3 lifetime end、§17.4 lifetime-preserving replace、§18.6 consume-out と ptr 非 retarget。Draft 17.19 の bounded `loan_write` clarification は既存 semantic rule を変えず、新しい exclusive / lifetime-ending / noalias authority を発行しない。今回はその source spelling / frontend correctness を証明しない。

## 既存 theorem inventory の監査

| Existing evidence | 結合に使う意味 |
| --- | --- |
| `RawReplace.target_after` | post root は currentFact/package だけを更新 |
| `replace_preserves_place_and_location` / `replace_preserves_incarnation` / `replace_preserves_governingDomain` | P/O/governing domain 保存という既存 claim |
| `RawReplace.newFact_ne_old` / `rawReplace_old_current_fact_not_live` / `replace_old_fact_remains_used` | current fact は変わり、old fact は dead、allocation history は保持 |
| `acquire_ref_matches_governing_domain` | pre-acquisition の exact location/incarnation/domain を target root と同定 |
| `ptr_remains_live_across_current_value_replace` | 同じ token/domain、post-state の stability/access premises で取得可能 |
| `acquire_ref_implies_governing_relation` | 取得先が actual live governing relation を持つ |
| `stale_ptr_after_take_cannot_acquire_ref` / `stale_ptr_after_destroy_cannot_acquire_ref` | lifetime end 後は同 token をどの evidence domain でも取得に使えない |
| `take_ends_incarnation` / `destroy_ends_incarnation` | end 後の global incarnation non-liveness |
| `take_then_reinitialize_does_not_revive_old_ptr` / `destroy_then_reinitialize_does_not_revive_old_ptr` | 既存 fresh restart control。今回は変更しない |
| `Counterexample.Reference` の initialized/replace/end witnesses | 既存 fixture と WF proof を再利用 |

既に replace/acquisition の局所合成 theorem と個別の lifecycle controls がある。今回の追加は、pre-acquisition から同じ target の対応を導く一般 theorem と、**同じ initialize → replace → end execution path** の具体的対比に限定した。

## 追加した machine-checked theorem

production は [`NewLang/F0/StableRoot.lean`](../NewLang/F0/StableRoot.lean) の `NewLang.F0.StableRoot`。state/datatype/transition relation は定義せず、proof-only の private target-match helper と四つの theorem だけを置く。

| Declaration | Result |
| --- | --- |
| `replace_preserves_preexisting_ptr_target` | pre-acquisition と legal replace から、同じ token location で live root、同じ place/incarnation/domain、new current fact、old fact と非同一、live Governs を導く。post access premise 不要 |
| `replace_preserves_preexisting_ptr_acquisition` | 上記の target 対応を導き、既存 replace/acquisition theorem へ渡す。post-state の stability/access を明示して同じ token/domain の acquisition を構成 |
| `replace_then_take_rejects_preexisting_ptr` | 同じ pre-token は replace 後の root の legal take で stale。任意の later stability/access proposition・evidence domain に対して取得不能 |
| `replace_then_destroy_rejects_preexisting_ptr` | 同じ対比を既存 Discardable / ending legality を満たす destroy に対して結合 |

post-state の stability/access proposition は pre-state と別 parameter にした。pre evidence が future access/loan を無条件に保証することを仮定しない。generic theorem は同一 `PtrToken` を使用し、new token を constructor で作り直したり incarnation を retarget したりしない。

### Concrete positive / negative contrast

既存 [`NewLang/F0/Counterexample/Reference.lean`](../NewLang/F0/Counterexample/Reference.lean) の private fixture を拡張し、public controls は三つだけ追加した。

| Declaration | Actual witness |
| --- | --- |
| `stable_root_replace_then_take_contrast` | initialize が incarnation 1 / fact 1 の ptr を発行 → pre-acquisition → legal replace が package B / fact 2 を install → 同じ place/incarnation/domain と同じ ptr の legal acquisition → legal take → incarnation dead、同 ptr の acquisition reject |
| `stable_root_replace_then_destroy_contrast` | 同じ initialize/pre-acquisition/replace/post-acquisition を経て、Discardable value の legal destroy → 同 ptr の acquisition reject |
| `stable_root_replace_still_requires_acquisition_guards` | replace 後も ptr は current だが old current fact は dead（history に保持）。missing stability、missing access、wrong governing domain の取得を reject。wrong domain も live なので単なる dead-domain 拒否ではない |

replace は P/O を保持しても VF を保持しない。この witness は ptr provenance と current-value dependency を同一視しない。old package / incoming / external survivor が invalidated fact に依存する場合の既存 replace legality を緩めていない。

concrete fixture の `True` premises は F0 の abstract caller obligations を満たす数学的 witness。production compiler が physical access / hidden stability を常に構成できるという claim ではない。take/destroy の legality も明示しており、replace に lifetime-ending authority を追加したり、ending operation の authority を省略したりしない。

## Proof / claim boundary

F0 `AcquireRef` は **point-of-acquisition derivation** であり、persistent ref result や lexical loan state を生成する transition ではない。従ってここで示すのは、既存 access/stability premises が post-state でも成立する時の potentially legal reacquisition と、その後の legal lifetime end との対比である。取得した ref を無条件に live のまま保持して root を終了できる、とは証明していない。

正式な product claim の範囲は stable-root mutation と ptr identity の分離。source `loan_write` / `loan_read_ptr` の checker correctness、全 future-use lifetime checking、field projection/mutation、recursive Node、raw storage/allocator、physical address、backend/noalias は scope 外。F3.1/global Safe Core implementation を開始しない。

## Audit、CI、review handback

既存 985 declarations の順序を保ち、新しい四 generic theorem と三 concrete controls を audit array 末尾へ追加する。計 **992 declarations**。private helper の依存も public theorem の `#print axioms` に反映される。whitelist は従来の `propext`, `Classical.choice`, `Quot.sound` のみ。project-owned Lean source の `sorry` / `axiom` / `admit` 使用は禁止のまま。

branch 上の最終 `lake build` / `bash scripts/check-proofs.sh` の結果、および PR exact head・pull_request-event `Lean proofs` run/job は [Issue #27 の Track: F handback](https://github.com/wakairo/NewLang_FormalProof/issues/27) に記録する。pin、manifest、bootstrap、workflow は変更しない。PR は open / unmerged で停止し、Issue の closure は Coordination に返す。

**FORMAL-LEMMA:** existing theorem の composition と同一 execution path の witness。**FORMAL-ENCODING:** ghost IDs / history / abstract access/stability は既存 non-normative encoding のまま。**FORMAL-SCOPE:** point acquisition と bounded flat-root integration に限定。新しい FORMAL-HOLE / FORMAL-AMBIGUITY / FORMAL-EXTRACTION、production/canonical semantics への finding は見つかっていない。

**F STABLE-ROOT INTEGRATION READY FOR REVIEW**
