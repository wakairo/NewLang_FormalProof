# F0.0 formalization notes

原資料は変更しない。Draft 17.4をnormative source of truthとして扱う。

- **FORMAL-ENCODING**: F0 reference shapeは`RootLocationId → Occupancy`であり、二つのlocationへ同じPlaceIdを割り当てた不正stateも表せる。異なるcurrent factsを持つrootを二つ作るだけで「一placeに一current fact」が崩れるため、`PlacesUnique`で排除した。carrierもlocationで区別し、同じpackageの二重installationを隠さない。これはnormative semanticsの変更ではなくWF-4をencodingに反映する処置。
- **FORMAL-ENCODING**: F0 §4.2で許容されるPlaceId/RootLocationIdの同一視は採用せず、nominalに区別した。WellFormedなlive rootsについてplaceとlocationが一対一になることをpredicateで表現した。incarnation identityのlive-root一意性も明示した。
- **FORMAL-SCOPE**: F0 §20.2/20.3はdomain transfer/finalizationを「F0.2」と呼ぶ一方、§28のproof sequenceではF0.2はstoreである。これはmilestone番号の不一致で、今回のF0.0 semanticsへ影響しない。次のmilestoneはユーザー指定と§28のF0.1 replaceに従う。domain operationsの番号整理は文書側で別途行えるが、添付原文は修正していない。
- **FORMAL-SCOPE**: finite-support、historical freshness、authorization、payload、authority conservation、structural places、scope/backing facts、transitionは今回未検証。F0.1以降で対応するpremise/invariantを明示する。特に「現在未使用」と「履歴を含めてfresh」を同一視しない。

F0.0の範囲で確認した関連節から、FORMAL-HOLE / FORMAL-AMBIGUITYに該当するsemantic defectは発見していない。これは仕様全体のsoundnessを証明したという意味ではない。
