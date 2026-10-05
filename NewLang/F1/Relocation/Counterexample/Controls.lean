import NewLang.F1.Relocation.Counterexample.Witness

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing
open Occupancy.Counterexample (geometry layout ty cid region rw)
noncomputable section

/-- These three controls target the historical allocation premises themselves;
no custom postcondition is substituted for the production relation. -/
theorem reused_root_incarnation_rejected (receipt : Receipt) (post : State) :
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅)
      {move .overlap with incarnation := ⟨0⟩} receipt post := by
  intro raw; exact raw.freshIncarnation (by simp [before,semantic])

theorem reused_source_current_fact_rejected (receipt : Receipt) (post : State) :
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅)
      {move .overlap with allocation := ⟨⟨0⟩,some (⟨3⟩,⟨1⟩)⟩} receipt post := by
  intro raw; exact raw.freshFacts.1 (by simp [before,semantic])

theorem reused_payload_occurrence_rejected (receipt : Receipt) (post : State) :
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅)
      {move .overlap with allocation := ⟨⟨2⟩,some (⟨3⟩,⟨0⟩)⟩} receipt post := by
  intro raw; exact (raw.freshFacts.2 ⟨3⟩ ⟨0⟩ rfl).2.2 (by simp [before,semantic])

theorem retired_occurrence_not_fresh :
    Conditional.Fact.occurrence ⟨9⟩ ∉ Conditional.LiveFacts (semantic ∅ ∅) ∧
    ¬ Conditional.FreshOccurrence (semantic ∅ ∅) ⟨9⟩ := by
  constructor
  · rintro ⟨l,live,occ⟩; have eq : l = source := by simpa [semantic] using live
    subst l; simp [semantic,root] at occ
  · simp [Conditional.FreshOccurrence,semantic]

/-- Same metadata endpoints can be fully valid accounting states and still
constitute the wrong relocation: source extent is not destination placement. -/
theorem transferred_source_placement_control :
    WellFormed geometry layout (before .disjoint rw ∅ ∅) ∧
    WellFormed geometry layout (after .equal rw ∅ ∅) ∧
    ¬ RawMove geometry sites ctx (before .disjoint rw ∅ ∅) (move .disjoint)
      (moveReceipt (before .disjoint rw ∅ ∅) (move .disjoint)) (after .equal rw ∅ ∅) := by
  refine ⟨independent_before_wellFormed _ _,independent_after_wellFormed _ _,?_⟩
  intro raw
  have wrong := raw.exact_placement_and_backing.2.1
  change some (srcExtent.placement geometry) = some ((dstExtent .disjoint).placement geometry) at wrong
  have unequal : some (srcExtent.placement geometry) ≠
      some ((dstExtent .disjoint).placement geometry) := by decide
  exact unequal wrong

/-- Only receipt identity changes; both complete endpoints remain well formed. -/
theorem copied_governing_relation_rejected :
    WellFormed geometry layout (after .overlap rw ∅ ∅) ∧
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅) (move .overlap)
      (.moved ⟨destination,⟨1⟩⟩ (governingKey (before .overlap rw ∅ ∅) source)) (after .overlap rw ∅ ∅) := by
  refine ⟨independent_after_wellFormed _ _,?_⟩
  intro raw
  have eq := raw.receipt_eq
  have unequal : Receipt.moved ⟨destination,⟨1⟩⟩ (governingKey (before .overlap rw ∅ ∅) source) ≠
      moveReceipt (before .overlap rw ∅ ∅) (move .overlap) := by decide
  exact unequal eq

theorem retargeted_old_ptr_receipt_rejected :
    WellFormed geometry layout (after .overlap rw ∅ ∅) ∧
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅) (move .overlap)
      (.moved ⟨destination,⟨0⟩⟩ ⟨⟨1⟩,⟨0⟩⟩) (after .overlap rw ∅ ∅) := by
  refine ⟨independent_after_wellFormed _ _,?_⟩
  intro raw
  have unequal : Receipt.moved ⟨destination,⟨0⟩⟩ ⟨⟨1⟩,⟨0⟩⟩ ≠
      moveReceipt (before .overlap rw ∅ ∅) (move .overlap) := by decide
  exact unequal raw.receipt_eq

def duplicated : State :=
  let s := after .overlap rw ∅ ∅
  {s with accounted := {s.accounted with base := {s.accounted.base with semantic :=
    {s.accounted.base.semantic with loosePackages := insert pkg s.accounted.base.semantic.loosePackages}}}}

theorem duplicated_package_breaks_only_carrier_rule :
    Occupancy.Accounting geometry layout (fun l => l ∈ duplicated.accounted.base.semantic.liveRoots)
      duplicated.accounted.base.physical duplicated.accounted.ledger ∧
    Conditional.DependenciesValid duplicated.accounted.base.semantic ∧
    ¬ WellFormed geometry layout duplicated := by
  refine ⟨(independent_after_wellFormed .overlap rw).accounting,independent_dependencies _ rfl,?_⟩
  intro wf
  exact wf.frame.installedNotLoose destination (by simp [duplicated,after,candidate,semanticCandidate,move])
    (by simp [duplicated,after,candidate,semanticCandidate,movedRoot,Conditional.installRoot,move,before,semantic,root])

/-- Implicit embedded-pointer repair leaves the endpoint invariant unchanged,
but violates exact transfer of value-owned package contents. -/
def fixedUp : State :=
  let s := after .overlap rw ∅ ∅
  {s with data := fun p => {s.data p with persistentPtrs := [⟨destination,⟨1⟩⟩]}}

theorem implicit_embedded_ptr_fixup_rejected :
    WellFormed geometry layout fixedUp ∧
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅) (move .overlap)
      (moveReceipt (before .overlap rw ∅ ∅) (move .overlap)) fixedUp := by
  have wf := independent_after_wellFormed .overlap rw
  refine ⟨⟨wf.toSumWellFormed,wf.ownedPresent,wf.ownedUnique⟩,?_⟩
  intro raw
  have contents := (raw.embedded_ptrs_and_owned_claims_not_fixed_up pkg).1
  have unequal : (fixedUp.data pkg).persistentPtrs ≠ ((before .overlap rw ∅ ∅).data pkg).persistentPtrs := by decide
  exact unequal contents

/-- Even fully valid end/restart endpoints at the exact same abstract range
are not the canonical identity action. -/
theorem same_extent_end_restart_rejected :
    WellFormed geometry layout (after .equal rw ∅ ∅) ∧
    ¬ Step geometry layout sites ctx (before .equal rw ∅ ∅) (.same source (cid 0) ty srcExtent)
      .identity (after .equal rw ∅ ∅) ∧
    ¬ RawMove geometry sites ctx (before .equal rw ∅ ∅) (move .equal)
      (moveReceipt (before .equal rw ∅ ∅) (move .equal)) (after .equal rw ∅ ∅) := by
  refine ⟨independent_after_wellFormed _ _,?_,?_⟩
  · intro step
    have eq := (same_place_is_exact_identity step.2.1).1
    have live := congrArg (fun s : State => s.accounted.base.semantic.liveRoots) eq
    have unequal : (after .equal rw ∅ ∅).accounted.base.semantic.liveRoots ≠
        (before .equal rw ∅ ∅).accounted.base.semantic.liveRoots := by decide
    exact unequal live
  · intro raw; exact raw.differentExtent rfl

/-- Numeric labels exist only in this counterexample. Equal labels grant no
identity or authority; distinct nominal regions have a legal distinct move. -/
theorem hypothetical_address_coincidence_does_not_equate_regions :
    (fun _ : BackingRegionId => 4096) (region 0) = (fun _ : BackingRegionId => 4096) (region 1) ∧
    region 0 ≠ region 1 ∧ srcExtent ≠ dstExtent .different ∧
    Step geometry layout sites ctx (before .different rw ∅ ∅) (.move (move .different))
      (moveReceipt (before .different rw ∅ ∅) (move .different)) (after .different rw ∅ ∅) :=
  ⟨rfl,by decide,by decide,different_region_relocation_is_legal⟩

end
end NewLang.F1.Relocation.Counterexample
