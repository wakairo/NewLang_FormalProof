import NewLang.F1.Relocation.Counterexample.Responsibility

namespace NewLang.F1.Relocation.Counterexample
open F0 Backing Occupancy
open Occupancy.Counterexample (geometry layout ty cid region rw)
noncomputable section

/-- Deliberately observable half-endpoint: all backing has raw responsibility,
no live root remains, and the old value is loose (or lost). The production
transition cannot publish either endpoint, even though it is well formed. -/
def halfSemantic (retain : Bool) : Conditional.State :=
  {semantic ∅ ∅ with liveRoots := ∅,loosePackages := if retain then {pkg,external} else {external}}
def halfLedger : Ledger :=
  {beforeLedger .overlap with claim := fun id => .storage ((beforeLedger .overlap).claim id).extent}
def half (retain : Bool) : State :=
  ⟨⟨⟨halfSemantic retain,⟨world .overlap rw,fun _ => none⟩⟩,halfLedger⟩,annotation .overlap⟩

private theorem half_invariant (retain : Bool) : Conditional.Invariant (halfSemantic retain) := by
  have base := before_invariant ∅ ∅
  constructor
  · constructor
    all_goals first | (intro l live; simp [halfSemantic] at live) | exact base.frame.domainCarrierCoherent
  · intro p _; by_cases same : p = pkg
    · subst p; exact ⟨.sum (sumValue ∅),by simp [halfSemantic,semantic]⟩
    · exact ⟨externalValue ∅,by simp [halfSemantic,semantic,same]⟩
  · intro p _ v present
    by_cases same : p = pkg
    · subst p
      have eq : v = sumValue ∅ := by simpa [Conditional.sumAt,halfSemantic,semantic,Conditional.SemanticValue.sumValue] using present.symm
      subst v; simp [Conditional.ValueTyped,halfSemantic,semantic,sumValue]
    · simp [Conditional.sumAt,halfSemantic,semantic,same,externalValue,Conditional.SemanticValue.sumValue] at present
  all_goals intro l live; simp [halfSemantic] at live

private theorem half_accounting (retain : Bool) :
    Accounting geometry layout (fun l => l ∈ (halfSemantic retain).liveRoots) (half retain).accounted.base.physical halfLedger := by
  have base := stage_accounting .overlap rw false
  constructor
  · constructor
    · exact base.geometry
    · exact base.regions
    · exact base.scopeLive
    · intro id active; exact base.inScope id active
    · intro id active; exact base.positive id active
    · intro id active; exact base.fits id active
    · intro id _; trivial
    · intro l; constructor
      · intro live; simp [halfSemantic] at live
      · rintro ⟨id,_,t,e,eq⟩; simp [halfLedger] at eq
    · intro l pl; constructor
      · intro placed; simp [half] at placed
      · rintro ⟨id,_,t,e,eq,_⟩; simp [halfLedger] at eq
  · intro i ia j ja neq
    simpa [halfLedger,Claim.extent,stageLedger] using base.disjoint i ia j ja neq
  · dsimp [ExpectedFootprint,half]; decide

/-- Ghost package data need not vanish when its carrier does; no package table
entry supplies surviving authority by itself. -/
theorem half_endpoints_wellFormed (retain : Bool) : WellFormed geometry layout (half retain) := by
  refine ⟨⟨half_invariant retain,independent_dependencies _ rfl,half_accounting retain⟩,?_,?_⟩
  · intro p _ id member
    by_cases same : p = pkg
    · subst p
      have eq : id = cid 2 := by simpa [half,annotation] using member
      subst id; constructor
      · change cid 2 ∈ halfLedger.active; decide
      · rfl
    · simp [half,annotation,same] at member
  · intro p q _ _ neq
    by_cases pp : p = pkg <;> by_cases qp : q = pkg
    · exact False.elim (neq (pp.trans qp.symm))
    all_goals simp [half,annotation,pp,qp]

theorem public_half_transition_rejected :
    WellFormed geometry layout (half true) ∧
    ¬ Step geometry layout sites ctx (before .overlap rw ∅ ∅) (.move (move .overlap))
      (moveReceipt (before .overlap rw ∅ ∅) (move .overlap)) (half true) :=
  ⟨half_endpoints_wellFormed true,no_recoverable_half_state (by simp [half,halfSemantic])⟩

theorem lost_semantic_package_rejected :
    WellFormed geometry layout (half false) ∧
    ¬ Conditional.Survives (half false).accounted.base.semantic pkg ∧
    ¬ RawMove geometry sites ctx (before .overlap rw ∅ ∅) (move .overlap)
      (moveReceipt (before .overlap rw ∅ ∅) (move .overlap)) (half false) := by
  have lost : ¬ Conditional.Survives (half false).accounted.base.semantic pkg := by
    simp [Conditional.Survives,half,halfSemantic,pkg,external]
  refine ⟨half_endpoints_wellFormed false,lost,?_⟩
  intro raw
  exact lost ((raw.all_survivors_retained pkg).mpr (Or.inr ⟨source,by simp [before,semantic],rfl⟩))

end
end NewLang.F1.Relocation.Counterexample
