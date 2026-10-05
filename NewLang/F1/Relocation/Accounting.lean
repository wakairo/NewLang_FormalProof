import NewLang.F1.Relocation.Proofs

namespace NewLang.F1.Relocation
open F0 Backing
noncomputable section

/-- The three regions are pairwise separated; their classification depends on
abstract bytes within nominal regions, not numeric address comparisons. -/
theorem three_way_partition (g : Occupancy.Geometry) (m : Move) :
    (sourceBytes g m \ destinationBytes g m) ∪ (sourceBytes g m ∩ destinationBytes g m) = sourceBytes g m ∧
    (destinationBytes g m \ sourceBytes g m) ∪ (sourceBytes g m ∩ destinationBytes g m) = destinationBytes g m ∧
    Disjoint (sourceBytes g m \ destinationBytes g m) (destinationBytes g m) := by
  constructor
  · ext b; by_cases src : b ∈ sourceBytes g m <;> by_cases dst : b ∈ destinationBytes g m <;> simp [src,dst]
  constructor
  · ext b; by_cases src : b ∈ sourceBytes g m <;> by_cases dst : b ∈ destinationBytes g m <;> simp [src,dst]
  · apply Finset.disjoint_left.mpr; intro b src dst
    exact (Finset.mem_sdiff.mp src).2 dst

namespace RawMove
variable {g : Occupancy.Geometry} {sites : RootSiteLayout} {ctx : Conditions} {s post : State}
    {m : Move} {receipt : Receipt}

theorem source_and_inputs_consumed (raw : RawMove g sites ctx s m receipt post) :
    m.sourceClaim ∉ post.accounted.ledger.active ∧
    ∀ id ∈ m.inputRaw, id ∉ post.accounted.ledger.active := by
  have sourceNotNew : m.sourceClaim ≠ m.newRootClaim := fun eq => raw.rootFresh (eq ▸ raw.sourceClaimPresent.1)
  have sourceNotOut : m.sourceClaim ∉ m.outputRaw := fun member => raw.outputFresh _ member raw.sourceClaimPresent.1
  rw [raw.post_eq]
  refine ⟨by simp [candidate,ledgerCandidate,sourceNotNew,sourceNotOut],?_⟩
  intro id input
  rcases raw.rawInputs id input with ⟨e,present⟩
  have notNew : id ≠ m.newRootClaim := fun eq => raw.rootFresh (eq ▸ present.1)
  have notOut : id ∉ m.outputRaw := fun member => raw.outputFresh id member present.1
  simp [candidate,ledgerCandidate,notNew,notOut,input]

theorem root_and_raw_outputs_produced (raw : RawMove g sites ctx s m receipt post) :
    Occupancy.Has post.accounted.ledger m.newRootClaim (.root m.type m.destination m.destinationExtent) ∧
    ∀ id ∈ m.outputRaw, Occupancy.Has post.accounted.ledger id (.storage (m.rawExtent id)) := by
  rw [raw.post_eq]
  refine ⟨⟨by simp [candidate,ledgerCandidate],by simp [candidate,ledgerCandidate]⟩,?_⟩
  intro id output
  have notRoot : id ≠ m.newRootClaim := fun eq => raw.rootNotRaw (eq ▸ output)
  exact ⟨by simp [candidate,ledgerCandidate,output],by simp [candidate,ledgerCandidate,notRoot,output]⟩

theorem occupancy_conserved (raw : RawMove g sites ctx s m receipt post) :
    Occupancy.TotalFootprint g post.accounted.ledger = Occupancy.TotalFootprint g s.accounted.ledger := by
  let framed := (s.accounted.ledger.active.erase m.sourceClaim) \ m.inputRaw
  let bytes := framed.biUnion (fun id => (s.accounted.ledger.claim id).extent.footprint g)
  have preTotal : Occupancy.TotalFootprint g s.accounted.ledger =
      bytes ∪ sourceBytes g m ∪ (destinationBytes g m \ sourceBytes g m) := by
    rw [← raw.inputCoverage]
    ext byte; constructor
    · rintro member
      rcases Finset.mem_biUnion.mp member with ⟨id,active,im⟩
      by_cases source : id = m.sourceClaim
      · subst id; exact Finset.mem_union_left _ (Finset.mem_union_right _ (by
          simpa [raw.sourceClaimPresent.2,Occupancy.Claim.extent,sourceBytes] using im))
      · by_cases input : id ∈ m.inputRaw
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨id,input,im⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨id,by simp [framed,Finset.mem_erase,active,source,input],im⟩))
    · rintro member
      rcases Finset.mem_union.mp member with left|input
      · rcases Finset.mem_union.mp left with frame|source
        · rcases Finset.mem_biUnion.mp frame with ⟨id,active,im⟩
          exact Finset.mem_biUnion.mpr ⟨id,(Finset.mem_erase.mp (Finset.mem_sdiff.mp active).1).2,im⟩
        · exact Finset.mem_biUnion.mpr ⟨m.sourceClaim,raw.sourceClaimPresent.1,by
            simpa [raw.sourceClaimPresent.2,Occupancy.Claim.extent,sourceBytes] using source⟩
      · rcases Finset.mem_biUnion.mp input with ⟨id,input,im⟩
        rcases raw.rawInputs id input with ⟨e,present⟩
        exact Finset.mem_biUnion.mpr ⟨id,present.1,im⟩
  have postTotal : Occupancy.TotalFootprint g post.accounted.ledger =
      bytes ∪ destinationBytes g m ∪ (sourceBytes g m \ destinationBytes g m) := by
    rw [← raw.outputCoverage,raw.post_eq]
    have frameEq : ∀ id ∈ framed, (ledgerCandidate s.accounted.ledger m).claim id = s.accounted.ledger.claim id := by
      intro id active
      have pre : id ∈ s.accounted.ledger.active := (Finset.mem_erase.mp (Finset.mem_sdiff.mp active).1).2
      have notRoot : id ≠ m.newRootClaim := fun eq => raw.rootFresh (eq ▸ pre)
      have notOut : id ∉ m.outputRaw := fun member => raw.outputFresh id member pre
      simp [ledgerCandidate,notRoot,notOut]
    ext byte; constructor
    · rintro member
      rcases Finset.mem_biUnion.mp member with ⟨id,active,im⟩
      have choices : id = m.newRootClaim ∨ id ∈ framed ∨ id ∈ m.outputRaw := by
        simpa [candidate,ledgerCandidate,framed,or_assoc] using active
      rcases choices with rfl|fr|out
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa [candidate,ledgerCandidate,destinationBytes,Occupancy.Claim.extent] using im))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨id,fr,by simpa only [candidate,frameEq id fr] using im⟩))
      · have notRoot : id ≠ m.newRootClaim := fun eq => raw.rootNotRaw (eq ▸ out)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨id,out,by
          simpa [candidate,ledgerCandidate,notRoot,out,Occupancy.Claim.extent] using im⟩)
    · rintro member
      rcases Finset.mem_union.mp member with left|out
      · rcases Finset.mem_union.mp left with fr|dest
        · rcases Finset.mem_biUnion.mp fr with ⟨id,active,im⟩
          exact Finset.mem_biUnion.mpr ⟨id,by simp [candidate,ledgerCandidate,framed] at active ⊢; exact Or.inr (Or.inl active),by
            simpa only [candidate,frameEq id active] using im⟩
        · exact Finset.mem_biUnion.mpr ⟨m.newRootClaim,by simp [candidate,ledgerCandidate],by
            simpa [candidate,ledgerCandidate,destinationBytes,Occupancy.Claim.extent] using dest⟩
      · rcases Finset.mem_biUnion.mp out with ⟨id,active,im⟩
        have notRoot : id ≠ m.newRootClaim := fun eq => raw.rootNotRaw (eq ▸ active)
        exact Finset.mem_biUnion.mpr ⟨id,by simp [candidate,ledgerCandidate,active],by
          simpa [candidate,ledgerCandidate,notRoot,active,Occupancy.Claim.extent] using im⟩
  rw [postTotal,preTotal]
  ext byte
  by_cases src : byte ∈ sourceBytes g m <;> by_cases dst : byte ∈ destinationBytes g m <;> simp [src,dst]

theorem intersection_never_returned_as_raw (raw : RawMove g sites ctx s m receipt post) :
    Disjoint (m.outputRaw.biUnion (fun id => (m.rawExtent id).footprint g))
      (sourceBytes g m ∩ destinationBytes g m) := by
  rw [raw.outputCoverage]
  apply Finset.disjoint_left.mpr
  intro byte out overlap; exact (Finset.mem_sdiff.mp out).2 (Finset.mem_inter.mp overlap).2

end RawMove
end
end NewLang.F1.Relocation
