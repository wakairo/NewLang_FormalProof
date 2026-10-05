import NewLang.F1.Occupancy.Claims

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

private theorem consumeOne_root_has_iff {s : Ledger} {source result : ClaimId} {new : Claim}
    (fresh : result ∉ s.active)
    (oldEmpty : ∀ t l e, s.claim source ≠ .root t l e)
    (newEmpty : ∀ t l e, new ≠ .root t l e) {id t l e} :
    Has (consumeOne s source result new) id (.root t l e) ↔ Has s id (.root t l e) := by
  constructor
  · rintro ⟨active,claim⟩
    rcases consumeOne_active_iff.mp active with rfl|⟨_,pre⟩
    · exact False.elim (newEmpty t l e (by simpa [consumeOne] using claim))
    · have other : id ≠ result := fun eq => fresh (eq ▸ pre)
      exact ⟨pre,by simpa [consumeOne,other] using claim⟩
  · rintro ⟨active,claim⟩
    have notSource : id ≠ source := by intro eq; subst id; exact oldEmpty t l e claim
    have notResult : id ≠ result := fun eq => fresh (eq ▸ active)
    exact ⟨consumeOne_active_iff.mpr (Or.inr ⟨notSource,active⟩),by simpa [consumeOne,notResult] using claim⟩

/-- Local empty-claim conversion lemma. Both old and new are explicitly non-root;
the physical/live layer is fixed. Lifetime transitions use their own relations. -/
theorem empty_conversion_preserves_accounting {g layout live p s}
    (wf : Accounting g layout live p s) {source result : ClaimId} {new : Claim}
    (active : source ∈ s.active) (fresh : result ∉ s.active)
    (sameExtent : new.extent = (s.claim source).extent) (typed : new.Typed layout)
    (oldEmpty : ∀ t l e, s.claim source ≠ .root t l e)
    (newEmpty : ∀ t l e, new ≠ .root t l e) :
    Accounting g layout live p (consumeOne s source result new) := by
  refine ⟨?_,?_,?_⟩
  · constructor
    · exact wf.geometry
    · exact wf.regions
    · exact wf.scopeLive
    · intro id ia
      rcases consumeOne_active_iff.mp ia with rfl|⟨_,pre⟩
      · simpa [consumeOne,sameExtent] using wf.inScope source active
      · have other : id ≠ result := fun eq => fresh (eq ▸ pre)
        simpa [consumeOne,other] using wf.inScope id pre
    · intro id ia
      rcases consumeOne_active_iff.mp ia with rfl|⟨_,pre⟩
      · simpa [consumeOne,sameExtent] using wf.positive source active
      · have other : id ≠ result := fun eq => fresh (eq ▸ pre)
        simpa [consumeOne,other] using wf.positive id pre
    · intro id ia
      rcases consumeOne_active_iff.mp ia with rfl|⟨_,pre⟩
      · simpa [consumeOne,sameExtent] using wf.fits source active
      · have other : id ≠ result := fun eq => fresh (eq ▸ pre)
        simpa [consumeOne,other] using wf.fits id pre
    · intro id ia
      rcases consumeOne_active_iff.mp ia with rfl|⟨_,pre⟩
      · simpa [consumeOne] using typed
      · have other : id ≠ result := fun eq => fresh (eq ▸ pre)
        simpa [consumeOne,other] using wf.typed id pre
    · intro l; constructor
      · intro live
        rcases (wf.roots l).mp live with ⟨id,ia,t,e,claim⟩
        have after := (consumeOne_root_has_iff fresh oldEmpty newEmpty).mpr ⟨ia,claim⟩
        exact ⟨id,after.1,t,e,after.2⟩
      · rintro ⟨id,ia,t,e,claim⟩
        have before := (consumeOne_root_has_iff fresh oldEmpty newEmpty).mp ⟨ia,claim⟩
        exact (wf.roots l).mpr ⟨id,before.1,t,e,before.2⟩
    · intro l pl; constructor
      · intro placed
        rcases (wf.placements l pl).mp placed with ⟨id,ia,t,e,claim,eq⟩
        have after := (consumeOne_root_has_iff fresh oldEmpty newEmpty).mpr ⟨ia,claim⟩
        exact ⟨id,after.1,t,e,after.2,eq⟩
      · rintro ⟨id,ia,t,e,claim,eq⟩
        have before := (consumeOne_root_has_iff fresh oldEmpty newEmpty).mp ⟨ia,claim⟩
        exact (wf.placements l pl).mpr ⟨id,before.1,t,e,before.2,eq⟩
  · intro a aa b ba different
    rcases consumeOne_active_iff.mp aa with rfl|⟨asrc,prea⟩
    · rcases consumeOne_active_iff.mp ba with rfl|⟨bsrc,preb⟩
      · exact False.elim (different rfl)
      · have br : b ≠ a := fun eq => fresh (eq ▸ preb)
        simpa [consumeOne,br,sameExtent] using wf.disjoint source active b preb bsrc.symm
    · have ar : a ≠ result := fun eq => fresh (eq ▸ prea)
      rcases consumeOne_active_iff.mp ba with rfl|⟨_,preb⟩
      · simpa [consumeOne,ar,sameExtent] using wf.disjoint a prea source active asrc
      · have br : b ≠ result := fun eq => fresh (eq ▸ preb)
        simpa [consumeOne,ar,br] using wf.disjoint a prea b preb different
  · rw [consumeOne_conserves_footprint g active fresh (congrArg (Extent.footprint g) sameExtent)]
    exact wf.coverage

theorem into_slot_step_of_raw {g layout aligned live p s source result t e post}
    (wf : Accounting g layout live p s) (raw : RawIntoSlot layout aligned s source result t e post) :
    IntoSlotStep g layout aligned live p s source result t e post := by
  refine ⟨wf,raw,?_⟩; rw [raw.post_eq]
  apply empty_conversion_preserves_accounting wf raw.sourceClaim.1 raw.resultFresh
  · rw [raw.sourceClaim.2]; rfl
  · exact raw.exactSize
  · intro t l f; rw [raw.sourceClaim.2]; simp
  · intros; simp

theorem erase_slot_step_of_raw {g layout live p s source result t e post}
    (wf : Accounting g layout live p s) (raw : RawEraseSlot s source result t e post) :
    EraseSlotStep g layout live p s source result t e post := by
  refine ⟨wf,raw,?_⟩; rw [raw.post_eq]
  apply empty_conversion_preserves_accounting wf raw.sourceClaim.1 raw.resultFresh
  · rw [raw.sourceClaim.2]; rfl
  · trivial
  · intro t l f; rw [raw.sourceClaim.2]; simp
  · intros; simp

theorem erase_slot_is_total {g layout live p s source t e}
    (wf : Accounting g layout live p s) (sourceClaim : Has s source (.slot t e)) :
    ∃ result post, EraseSlotStep g layout live p s source result t e post := by
  rcases erase_slot_has_no_access_precondition sourceClaim with ⟨result,post,raw⟩
  exact ⟨result,post,erase_slot_step_of_raw wf raw⟩

theorem empty_claim_conversion_preserves_flat {g layout : _} {s : State} {post : Ledger}
    (wf : WellFormed g layout s)
    (accounting : Accounting g layout (FlatLive s.flat.semantic) s.flat.physical post) :
    WellFormed g layout ⟨s.flat,post⟩ := ⟨wf.toWellFormed,accounting⟩

theorem empty_claim_conversion_preserves_sum {g layout : _} {s : SumState} {post : Ledger}
    (wf : SumWellFormed g layout s)
    (accounting : Accounting g layout (fun l => l ∈ s.base.semantic.liveRoots) s.base.physical post) :
    SumWellFormed g layout ⟨s.base,post⟩ := ⟨wf.toInvariant,wf.dependencies,accounting⟩

end
end NewLang.F1.Occupancy
