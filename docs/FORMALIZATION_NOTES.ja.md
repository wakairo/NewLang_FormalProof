# F0.0 / F0.1 formalization notes

Draft 17.4をnormative source of truthとして維持し、変更していません。non-normative bridgeの編集修正は以下へ記録します。

- **FORMAL-EXTRACTION — F0.1前に解決**: 元のF0 Draft 0にあったmilestone番号の衝突を§20.2・§20.3・§24 traceability tableで修正し、§28へF0.6を追加しました。LifetimeDomain transfer/finalizationはF0.6、F0.2はstoreです。semantic ruleは変更していません。F0.0ではscope/roadmapの不一致として記録していた問題について、その履歴と解決を保持します。
- **FORMAL-ENCODING — F0.0から維持**: `RootLocationId → Occupancy`は同じPlaceIdと異なるcurrent factsを持つ二つのlocationを表せます。`PlacesUnique`によりこの不正stateを排除してWF-4を表現します。location-based carrierはpackageの二重installationも隠しません。F0.1のold-fact invalidation証明では、他rootが同じplaceのold factをliveに保つ可能性をplace uniquenessで排除します。
- **FORMAL-ENCODING — F0.0から維持**: F0 §4.2で許容されたPlaceId/RootLocationIdの同一視は採用せずnominalに分離しています。WellFormedなlive rootsのplace/location対応とincarnation identityの一意性をpredicateで表現します。
- **FORMAL-ENCODING — F0.1 history**: `usedValueFacts : Finset ValueFactId`はproof-only ghost stateです。`ValueFactsRecorded`はcurrent factを履歴へ含め、`FreshValueFact`は過去の割当てすべてを除外します。Raw replaceは新factをinsertし、retired factを削除しません。history monotonicityと、currently deadでもhistorically usedであり得るcountermodelを証明しました。初期状態には過去の履歴をすべて記録し、将来のallocating operationも履歴を拡張する必要があります。runtime/compilerのhistory storageは要求しません。F0.4のusedIncarnationsへ同じ方式で拡張可能ですが今回は未実装です。
- **FORMAL-LEMMA — F0.1 non-laundering**: Preservation theoremはlegal Stepのpost-state条件をprojectします。意味のあるnegative proofでは、raw candidateの具体的更新、old-fact invalidation、dependency dataの保存、old-package survivalを結合します。incoming caseも同じinvalidation lemmaを使います。すべてのraw candidateがWellFormedであるとは仮定しません。independentなlegal例でvacuityを排除し、dependency checkを省いたcountermodelでは他invariantがすべて成立することを確認しています。
- **FORMAL-SCOPE — 残るscope**: 実装したoperationはreplaceのみです。borrow checker/type compatibilityのderivationはcallerが証明するProp premiseで、production側で常にTrueにはしません。exclusive/lifetime-ending authorityはreplaceへ要求しません。finite-support proof、incarnation allocation history、payload、authority conservation、structural places、scope/backing facts、他operationはscope外です。

F0.0/F0.1で確認した関連節からFORMAL-HOLE / FORMAL-AMBIGUITYは発見していません。malformed raw candidateはdependency checkを省いた意図的break-testであり、normative legal replace ruleへの反例ではありません。仕様全体のsoundnessも主張しません。
