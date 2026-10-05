import NewLang.F1.Swap

namespace NewLang.F1.Counterexample.RootTransition
open F0
noncomputable section

private def l0 : RootLocationId := ⟨0⟩
private def l1 : RootLocationId := ⟨1⟩
private def rootAt (l : RootLocationId) : StructuredRoot :=
  let p : PlaceId := if l = l0 then ⟨0⟩ else ⟨1⟩
  ⟨⟨{p},p,fun _=>[]⟩,fun _=>⟨⟨p.index⟩,⟨p.index⟩,∅⟩,⟨p.index⟩,⟨p.index⟩,false⟩
private def initial : CurrentState where
  base := {
    liveRoots := {l0,l1}
    root := rootAt
    loosePackages := ∅
    looseValues := fun _=>none
    liveDomains := {⟨0⟩,⟨1⟩}
    domainValueCarrier := fun d => if d = ⟨0⟩ ∨ d = ⟨1⟩ then some ⟨0⟩ else none
    usedValueFacts := {⟨0⟩,⟨1⟩}
    usedIncarnations := {⟨0⟩,⟨1⟩} }
  content := fun l _=>l.index
  capability := fun _ _=>false
  carried := fun _=>none
private def left : StructuralTarget := ⟨l0,⟨0⟩⟩
private def right : StructuralTarget := ⟨l1,⟨1⟩⟩
private def fresh (q : NodeKey) : ValueFactId := ⟨10+q.2.index⟩
private def post : CurrentState := structuralSwapCandidate initial left right fresh

private theorem nodes {l : RootLocationId} {p : PlaceId} (live : LiveNode initial.base l p) :
    (l = l0 ∧ p = ⟨0⟩) ∨ (l = l1 ∧ p = ⟨1⟩) := by
  have loc : l = l0 ∨ l = l1 := by simpa [LiveNode,initial] using live.1
  rcases loc with rfl|rfl
  · left; refine ⟨rfl,?_⟩; simpa [initial,rootAt] using live.2
  · right; refine ⟨rfl,?_⟩; simpa [initial,rootAt,l0,l1] using live.2

private theorem initial_wf : CurrentWellFormed initial := by
  refine ⟨?_,by simp [initial],fun _ _=>rfl⟩
  constructor
  · intro l _; constructor
    · simp [initial,rootAt]
    · rfl
    · intro p pt q qt _; exact (Finset.mem_singleton.mp pt).trans (Finset.mem_singleton.mp qt).symm
    · intro p pt nonroot; exact False.elim (nonroot (Finset.mem_singleton.mp pt))
  · intro l m p lp mp
    rcases nodes lp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases nodes mp with ⟨rfl,eq⟩|⟨rfl,eq⟩ <;> simp_all [l0,l1]
  · intro l p m q lp mq same
    rcases nodes lp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases nodes mq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp_all [initial,rootAt,l0,l1]
  · intro l p m q lp mq same
    rcases nodes lp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rcases nodes mq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp_all [initial,rootAt,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [initial] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [initial] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [initial,rootAt,l0,l1]
  · intro l _; simp [initial]
  · simp [initial]
  · intro l lt; have lc : l = l0 ∨ l = l1 := by simpa [initial] using lt
    rcases lc with rfl|rfl <;> simp [initial,rootAt,l0,l1]
  · intro l p _ f dep; simp [LocalDeps,initial,rootAt] at dep
  · simp [initial]
  · intro l p live; rcases nodes live with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [initial,rootAt,l0,l1]
  · intro l p live; rcases nodes live with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [initial,rootAt,l0,l1]
  · intro d; by_cases present : d = ⟨0⟩ ∨ d = ⟨1⟩ <;> simp [initial,present]

private theorem raw : RawStructuralSwapDistinct True True initial left right fresh post := by
  classical
  constructor
  · exact ⟨by simp [initial,left],by simp [initial,left,rootAt]⟩
  · exact ⟨by simp [initial,right],by simp [initial,right,rootAt,l0,l1]⟩
  · exact Or.inl (by decide)
  · refine ⟨?_,fun _ _=>rfl⟩
    simp [extractValue,subtreePlaces,initial,left,right,rootAt,Finset.filter_singleton,Below,Ancestor,relativePosition,l0,l1]
  · refine ⟨?_,fun _ _=>rfl⟩
    simp [extractValue,subtreePlaces,initial,left,right,rootAt,Finset.filter_singleton,Below,Ancestor,relativePosition,l0,l1]
  · constructor
    · intro q qc
      have live : LiveNode initial.base q.1 q.2 := by
        rcases Finset.mem_union.mp qc with lhs|rhs
        · exact (mem_affectedBy.mp lhs).1
        · exact (mem_affectedBy.mp rhs).1
      rcases nodes live with ⟨l,p⟩|⟨l,p⟩ <;> simp [initial,fresh,p]
    · intro q qc r rc same
      have live : ∀ key ∈ swapAffected initial.base left right, LiveNode initial.base key.1 key.2 := by
        intro key member
        rcases Finset.mem_union.mp member with lhs|rhs
        · exact (mem_affectedBy.mp lhs).1
        · exact (mem_affectedBy.mp rhs).1
      rcases nodes (live q qc) with ⟨ql,qp⟩|⟨ql,qp⟩ <;>
        rcases nodes (live r rc) with ⟨rl,rp⟩|⟨rl,rp⟩ <;>
        simp_all [fresh] <;> exact Prod.ext (ql.trans rl.symm) (qp.trans rp.symm)
  · trivial
  · trivial
  · rfl

private theorem post_wf : CurrentWellFormed post := by
  classical
  have wf := initial_wf
  refine ⟨?_,by simp [post,structuralSwapCandidate,refreshCurrentFacts,initial],fun _ _=>rfl⟩
  refine { wf.structural with
    currentFactsUnique := ?_
    installedUnique := ?_
    installedNotLoose := ?_
    localDependenciesValid := ?_
    valueFactsRecorded := ?_
    looseDependenciesValid := by intro pkg loose; change pkg ∈ (∅ : Finset PackageId) at loose; simp at loose }
  · intro l p m q lp mq same
    exact refreshed_current_facts_unique wf.structural raw.fresh_facts lp mq same
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [post,structuralSwapCandidate,refreshCurrentFacts,initial] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [post,structuralSwapCandidate,refreshCurrentFacts,initial] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;>
      simp_all [post,structuralSwapCandidate,initial,left,right,rootAt,l0,l1]
  · intro l _; change _ ∉ (∅ : Finset PackageId); simp
  · intro l p _ f dep
    have emptyLeft : ∀ k, ((extractValue initial left).fragment k).dependencies = ∅ := fun _=>rfl
    have emptyRight : ∀ k, ((extractValue initial right).fragment k).dependencies = ∅ := fun _=>rfl
    simp only [post,structuralSwapCandidate,LocalDeps] at dep
    split at dep
    · simp only [Option.map_some,Option.getD_some,emptyRight] at dep
      exact False.elim (Finset.notMem_empty f dep)
    · split at dep
      · simp only [Option.map_some,Option.getD_some,emptyLeft] at dep
        exact False.elim (Finset.notMem_empty f dep)
      · change f ∈ (∅ : Finset Fact) at dep
        exact False.elim (Finset.notMem_empty f dep)
  · intro l p live; exact refreshed_current_facts_recorded wf.structural _ _ live

theorem whole_root_swap_is_legal : StructuralSwapStep True True initial left right post :=
  ⟨initial_wf,RawStructuralSwap.distinct raw,post_wf⟩

theorem whole_root_swap_erasure_observations :
    F0.WellFormed (eraseToF0 post.base) ∧
    (post.base.root l0).package = (initial.base.root l1).package ∧
    (post.base.root l1).package = (initial.base.root l0).package ∧
    (eraseRoot (post.base.root l0)).incarnation = ⟨0⟩ := by
  have carriers := swap_whole_root_carriers_are_exchanged raw rfl rfl
  exact ⟨f1_wellFormed_erases_to_f0_wellFormed post_wf.structural,carriers.1,carriers.2,rfl⟩

end
end NewLang.F1.Counterexample.RootTransition
