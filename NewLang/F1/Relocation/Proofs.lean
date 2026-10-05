import NewLang.F1.Relocation.Model

namespace NewLang.F1.Relocation
open F0 Backing
noncomputable section

theorem same_place_is_exact_identity {g sites ctx s l id t e receipt post}
    (raw : RawRelocate g sites ctx s (.same l id t e) receipt post) : post = s ∧ receipt = .identity := by
  cases raw; exact ⟨rfl,rfl⟩

theorem same_place_is_legal {g layout sites ctx s l id t e} (wf : WellFormed g layout s)
    (identified : ctx.identified) (live : l ∈ s.accounted.base.semantic.liveRoots)
    (root : Occupancy.Has s.accounted.ledger id (.root t l e)) :
    Step g layout sites ctx s (.same l id t e) .identity s := ⟨wf,.same identified live root,wf⟩

theorem same_place_preserves_token_and_accounting {g sites ctx s l id t e receipt post}
    (raw : RawRelocate g sites ctx s (.same l id t e) receipt post) (ptr : PtrToken) :
    (CurrentToken post ptr ↔ CurrentToken s ptr) ∧ post.accounted = s.accounted ∧ post.data = s.data := by
  rw [(same_place_is_exact_identity raw).1]; exact ⟨Iff.rfl,rfl,rfl⟩

/-- No parallel provenance logic: root-level currentness agrees exactly with
F0 after the already-reviewed conditional/structural state erasure. -/
theorem current_token_erases_to_f0 (s : State) (ptr : PtrToken) :
    CurrentToken s ptr ↔ F0.CurrentPtr (F1.eraseToF0 (Conditional.erase s.accounted.base.semantic).base) ptr := by
  constructor
  · rintro ⟨live,inc⟩
    exact ⟨F1.eraseRoot ((Conditional.erase s.accounted.base.semantic).base.root ptr.location),
      (F1.erase_occupancy_live_iff _ _ _).mpr ⟨live,rfl⟩,inc⟩
  · rintro ⟨r,live,inc⟩
    rcases (F1.erase_occupancy_live_iff _ _ _).mp live with ⟨present,eq⟩
    exact ⟨present,by simpa [← eq,F1.eraseRoot,Conditional.erase] using inc⟩

namespace RawMove
variable {g : Occupancy.Geometry} {sites : RootSiteLayout} {ctx : Conditions} {s post : State}
  {m : Move} {receipt : Receipt}

theorem live_after (raw : RawMove g sites ctx s m receipt post) (l : RootLocationId) :
    l ∈ post.accounted.base.semantic.liveRoots ↔ l = m.destination ∨
      (l ≠ m.source ∧ l ∈ s.accounted.base.semantic.liveRoots) := by
  rw [raw.post_eq]; simp [candidate,semanticCandidate,Finset.mem_erase]

theorem source_ended_destination_started (raw : RawMove g sites ctx s m receipt post) :
    m.source ∉ post.accounted.base.semantic.liveRoots ∧ m.destination ∈ post.accounted.base.semantic.liveRoots := by
  rw [live_after raw,live_after raw]
  exact ⟨by simp [raw.differentLocation],Or.inl rfl⟩

theorem destination_root (raw : RawMove g sites ctx s m receipt post) :
    post.accounted.base.semantic.root m.destination = movedRoot sites s.accounted.base.semantic m := by
  rw [raw.post_eq]; simp [candidate,semanticCandidate]

theorem other_root (raw : RawMove g sites ctx s m receipt post) {l : RootLocationId}
    (other : l ≠ m.destination) : post.accounted.base.semantic.root l = s.accounted.base.semantic.root l := by
  rw [raw.post_eq]; simp [candidate,semanticCandidate,other]

theorem package_and_authority_data_unchanged (raw : RawMove g sites ctx s m receipt post) :
    post.accounted.base.semantic.values = s.accounted.base.semantic.values ∧ post.data = s.data ∧
    post.accounted.base.semantic.loosePackages = s.accounted.base.semantic.loosePackages := by
  rw [raw.post_eq]; exact ⟨rfl,rfl,rfl⟩

theorem same_domain_fresh_relation (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post) :
    (post.accounted.base.semantic.root m.destination).governing =
      (s.accounted.base.semantic.root m.source).governing ∧
    governingKey post m.destination ≠ governingKey s m.source := by
  refine ⟨by rw [destination_root raw]; rfl,?_⟩
  intro same
  have inc : m.incarnation = (s.accounted.base.semantic.root m.source).incarnation := by
    simpa [governingKey,destination_root raw,movedRoot] using congrArg Prod.fst same
  exact raw.freshIncarnation (inc.symm ▸ wf.frame.incarnationsRecorded m.source raw.sourceLive)

theorem destination_does_not_inherit_place (raw : RawMove g sites ctx s m receipt post) :
    (post.accounted.base.semantic.root m.destination).place ≠ (s.accounted.base.semantic.root m.source).place := by
  rw [destination_root raw]
  change sites.placeAt m.destination ≠ _
  rw [raw.sourceSite]
  exact fun eq => raw.differentLocation (sites.injective eq).symm

theorem fresh_incarnation_and_history (raw : RawMove g sites ctx s m receipt post) :
    (post.accounted.base.semantic.root m.destination).incarnation = m.incarnation ∧
    m.incarnation ∉ s.accounted.base.semantic.usedIncarnations ∧
    m.incarnation ∈ post.accounted.base.semantic.usedIncarnations ∧
    s.accounted.base.semantic.usedIncarnations ⊆ post.accounted.base.semantic.usedIncarnations := by
  refine ⟨by rw [destination_root raw]; rfl,raw.freshIncarnation,?_,?_⟩
  · rw [raw.post_eq]; simp [candidate,semanticCandidate]
  · rw [raw.post_eq]; exact Finset.subset_insert _ _

theorem fresh_current_and_occurrence_history (raw : RawMove g sites ctx s m receipt post) :
    Conditional.FreshAllocation s.accounted.base.semantic m.allocation ∧
    (post.accounted.base.semantic.root m.destination).currentFact = m.allocation.current ∧
    (post.accounted.base.semantic.root m.destination).occurrence = m.allocation.payload.map Prod.snd ∧
    s.accounted.base.semantic.usedValueFacts ⊆ post.accounted.base.semantic.usedValueFacts ∧
    s.accounted.base.semantic.usedOccurrences ⊆ post.accounted.base.semantic.usedOccurrences := by
  refine ⟨raw.freshFacts,by rw [destination_root raw]; rfl,by rw [destination_root raw]; rfl,?_,?_⟩
  · rw [raw.post_eq]; exact Finset.subset_union_left
  · rw [raw.post_eq]; exact Finset.subset_union_left

theorem allocations_recorded (raw : RawMove g sites ctx s m receipt post) :
    m.allocation.facts ⊆ post.accounted.base.semantic.usedValueFacts ∧
    m.allocation.occurrences ⊆ post.accounted.base.semantic.usedOccurrences := by
  rw [raw.post_eq]; exact ⟨Finset.subset_union_right,Finset.subset_union_right⟩

/-- The bounded fixed structure is the existing singleton root layout. Its
sole fixed incarnation is the fresh root incarnation, not the source identity. -/
theorem erased_fixed_root_is_fresh (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post) :
    ((Conditional.erase post.accounted.base.semantic).base.root m.destination).layout.places = {sites.placeAt m.destination} ∧
    (((Conditional.erase post.accounted.base.semantic).base.root m.destination).node
      (sites.placeAt m.destination)).incarnation = m.incarnation ∧
    m.incarnation ≠ (s.accounted.base.semantic.root m.source).incarnation := by
  refine ⟨by simp [Conditional.erase,destination_root raw,movedRoot],by change (post.accounted.base.semantic.root m.destination).incarnation = m.incarnation; rw [destination_root raw]; rfl,?_⟩
  intro same; exact raw.freshIncarnation (same.symm ▸ wf.frame.incarnationsRecorded m.source raw.sourceLive)

theorem old_root_fact_not_live (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post) :
    Conditional.Fact.fixed (.valueFact (s.accounted.base.semantic.root m.source).place
      (s.accounted.base.semantic.root m.source).currentFact) ∉ Conditional.LiveFacts post.accounted.base.semantic := by
  rintro ⟨l,live,place,fact⟩
  rcases (live_after raw l).mp live with rfl|⟨other,pre⟩
  · rw [destination_root raw] at fact
    change m.allocation.current = _ at fact
    exact raw.freshFacts.1 (fact.symm ▸ wf.frame.valueFactsRecorded m.source raw.sourceLive)
  · rw [other_root raw (by intro eq; subst l; exact raw.destinationVacant pre)] at place
    exact other (wf.frame.placesUnique l pre m.source raw.sourceLive place)

theorem old_occurrence_not_live (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post)
    {o : Conditional.OccurrenceId} (old : (s.accounted.base.semantic.root m.source).occurrence = some o) :
    Conditional.Fact.occurrence o ∉ Conditional.LiveFacts post.accounted.base.semantic := by
  rintro ⟨l,live,occ⟩
  rcases (live_after raw l).mp live with rfl|⟨other,pre⟩
  · rw [destination_root raw] at occ
    change m.allocation.payload.map Prod.snd = some o at occ
    cases alloc : m.allocation.payload with
    | none => simp [alloc] at occ
    | some pair =>
      have eq : pair.2 = o := by simpa [alloc] using occ
      exact (raw.freshFacts.2 pair.1 pair.2 alloc).2.2 (eq.symm ▸ wf.occurrencesRecorded m.source raw.sourceLive o old)
  · rw [other_root raw (by intro eq; subst l; exact raw.destinationVacant pre)] at occ
    exact other (wf.occurrencesUnique l pre m.source raw.sourceLive o occ old)

theorem old_payload_fact_not_live (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post)
    {o : Conditional.OccurrenceId} (old : (s.accounted.base.semantic.root m.source).occurrence = some o)
    (fact : ValueFactId) : Conditional.Fact.payloadValue o fact ∉ Conditional.LiveFacts post.accounted.base.semantic := by
  rintro ⟨l,live,occ,_⟩
  exact old_occurrence_not_live wf raw old ⟨l,live,occ⟩

theorem all_survivors_retained (raw : RawMove g sites ctx s m receipt post) (pkg : PackageId) :
    Conditional.Survives post.accounted.base.semantic pkg ↔ Conditional.Survives s.accounted.base.semantic pkg := by
  have loose := (package_and_authority_data_unchanged raw).2.2
  constructor
  · rintro (lp|⟨l,live,eq⟩)
    · exact Or.inl (loose ▸ lp)
    · rcases (live_after raw l).mp live with rfl|⟨_,pre⟩
      · exact Or.inr ⟨m.source,raw.sourceLive,by simpa [destination_root raw,movedRoot,Conditional.installRoot] using eq⟩
      · exact Or.inr ⟨l,pre,by rw [other_root raw (by intro same; subst l; exact raw.destinationVacant pre)] at eq; exact eq⟩
  · rintro (lp|⟨l,live,eq⟩)
    · exact Or.inl (loose.symm ▸ lp)
    · by_cases source : l = m.source
      · subst l
        exact Or.inr ⟨m.destination,(source_ended_destination_started raw).2,by
          simpa [destination_root raw,movedRoot,Conditional.installRoot] using eq⟩
      · exact Or.inr ⟨l,(live_after raw l).mpr (Or.inr ⟨source,live⟩),by
          rw [other_root raw (by intro same; subst l; exact raw.destinationVacant live)]; exact eq⟩

theorem package_installed_once (wf : WellFormed g layout post) (raw : RawMove g sites ctx s m receipt post) :
    ∃! l, l ∈ post.accounted.base.semantic.liveRoots ∧
      (post.accounted.base.semantic.root l).package = (s.accounted.base.semantic.root m.source).package := by
  refine ⟨m.destination,⟨(source_ended_destination_started raw).2,by rw [destination_root raw]; rfl⟩,?_⟩
  rintro l ⟨live,eq⟩
  exact wf.frame.installedUnique l live m.destination (source_ended_destination_started raw).2
    (eq.trans (by rw [destination_root raw]; rfl))

theorem old_token_stale (raw : RawMove g sites ctx s m receipt post) :
    ¬ CurrentToken post ⟨m.source,(s.accounted.base.semantic.root m.source).incarnation⟩ :=
  fun h => (source_ended_destination_started raw).1 h.1

theorem old_incarnation_cannot_revive (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post) :
    ∀ l ∈ post.accounted.base.semantic.liveRoots,
      (post.accounted.base.semantic.root l).incarnation ≠ (s.accounted.base.semantic.root m.source).incarnation := by
  intro l live same
  rcases (live_after raw l).mp live with rfl|⟨other,pre⟩
  · rw [destination_root raw] at same
    change m.incarnation = _ at same
    exact raw.freshIncarnation (same.symm ▸ wf.frame.incarnationsRecorded m.source raw.sourceLive)
  · rw [other_root raw (by intro eq; subst l; exact raw.destinationVacant pre)] at same
    exact other (wf.frame.incarnationsUnique l pre m.source raw.sourceLive same)

theorem fresh_destination_token (raw : RawMove g sites ctx s m receipt post) :
    CurrentToken post ⟨m.destination,m.incarnation⟩ ∧
    (⟨m.destination,m.incarnation⟩ : PtrToken) ≠ ⟨m.source,(s.accounted.base.semantic.root m.source).incarnation⟩ :=
  ⟨⟨(source_ended_destination_started raw).2,by rw [destination_root raw]; rfl⟩,
    fun eq => raw.differentLocation (congrArg PtrToken.location eq).symm⟩

theorem exact_placement_and_backing (raw : RawMove g sites ctx s m receipt post) :
    post.accounted.base.physical.placement m.source = none ∧
    post.accounted.base.physical.placement m.destination = some (m.destinationExtent.placement g) ∧
    post.accounted.base.physical.world = s.accounted.base.physical.world := by
  rw [raw.post_eq]
  simp [candidate,physicalCandidate,startPlacement,endPlacement,raw.differentLocation]

theorem fresh_receipt_not_copied (raw : RawMove g sites ctx s m receipt post) :
    receipt = .moved ⟨m.destination,m.incarnation⟩
      ⟨m.incarnation,(s.accounted.base.semantic.root m.source).governing⟩ := raw.receipt_eq

theorem embedded_ptrs_and_owned_claims_not_fixed_up (raw : RawMove g sites ctx s m receipt post) (pkg : PackageId) :
    (post.data pkg).persistentPtrs = (s.data pkg).persistentPtrs ∧
    (post.data pkg).ownedClaims = (s.data pkg).ownedClaims ∧
    (post.data pkg).opaqueAuthority = (s.data pkg).opaqueAuthority := by
  rw [(package_and_authority_data_unchanged raw).2.1]; exact ⟨rfl,rfl,rfl⟩

theorem retired_incarnation_stays_unallocatable (wf : WellFormed g layout s) (raw : RawMove g sites ctx s m receipt post)
    {later : Conditional.State} (history : post.accounted.base.semantic.usedIncarnations ⊆ later.usedIncarnations) :
    (s.accounted.base.semantic.root m.source).incarnation ∈ later.usedIncarnations :=
  history ((fresh_incarnation_and_history raw).2.2.2 (wf.frame.incarnationsRecorded m.source raw.sourceLive))

end RawMove

theorem step_preserves_wellFormed {g layout sites ctx s action receipt post}
    (step : Step g layout sites ctx s action receipt post) : WellFormed g layout post := step.2.2

theorem step_has_unique_byte_responsibility {g layout sites ctx s action receipt post}
    (step : Step g layout sites ctx s action receipt post) {byte : AbstractByteId}
    (covered : byte ∈ Occupancy.ExpectedFootprint post.accounted.base.physical post.accounted.ledger) :
    ∃! id, id ∈ post.accounted.ledger.active ∧ byte ∈ (post.accounted.ledger.claim id).extent.footprint g :=
  Occupancy.every_scoped_byte_has_unique_responsibility step.2.2.accounting covered

theorem move_rejects_surviving_old_occurrence_dependency {g layout sites ctx s m receipt post}
    (wf : WellFormed g layout s) {pkg : PackageId} (survives : Conditional.Survives s.accounted.base.semantic pkg)
    {value : Conditional.SemanticValue} (data : s.accounted.base.semantic.values pkg = some value)
    {o : Conditional.OccurrenceId} (old : (s.accounted.base.semantic.root m.source).occurrence = some o)
    (dep : Conditional.Fact.occurrence o ∈ value.dependencies) :
    ¬ Step g layout sites ctx s (.move m) receipt post := by
  rintro ⟨_,raw,after⟩; cases raw with
  | move moved =>
    apply moved.old_occurrence_not_live wf old
    exact after.dependencies pkg ((moved.all_survivors_retained pkg).mpr survives) value
      (by rw [moved.package_and_authority_data_unchanged.1]; exact data) _ dep

theorem no_recoverable_half_state {g layout sites ctx s m receipt post}
    (half : m.destination ∉ post.accounted.base.semantic.liveRoots) :
    ¬ Step g layout sites ctx s (.move m) receipt post := by
  rintro ⟨_,raw,_⟩; cases raw with | move moved => exact half moved.source_ended_destination_started.2

end
end NewLang.F1.Relocation
