import NewLang.F1.Conditional.Proofs

namespace NewLang.F1.Conditional.Counterexample.Sum
open F0
noncomputable section

private def l0 : RootLocationId := ⟨0⟩
private def l1 : RootLocationId := ⟨1⟩
private def pkg (n : Nat) : PackageId := ⟨n⟩
private def occ (n : Nat) : OccurrenceId := ⟨n⟩
private def vf (n : Nat) : ValueFactId := ⟨n⟩
private def nominal : SumTypeId := ⟨0⟩
private def sumType (cap : Bool) : SumType :=
  ⟨{⟨0⟩,⟨1⟩,⟨2⟩},fun v => v.index != 0,fun _ => cap⟩
private def value (variant : Nat) (deps : Finset Fact) : SumValue :=
  ⟨nominal,⟨variant⟩,∅,if variant = 0 then none else some ⟨variant+10,deps⟩⟩

/-- Two sum roots, one incoming sum, one external survivor, one incoming payload.
Occurrence 9 is retired history: it is not currently live. -/
private def fixture (oldVariant newVariant : Nat) (cap : Bool)
    (oldDeps rightDeps newDeps externalDeps payloadDeps : Finset Fact) : State where
  liveRoots := {l0,l1}
  root := fun l => {
    place := ⟨l.index⟩
    incarnation := ⟨l.index⟩
    currentFact := vf l.index
    package := pkg l.index
    governing := ⟨0⟩
    typeId := nominal
    occurrence := if l = l0 ∧ oldVariant = 0 then none else some (occ l.index)
    payloadFact := if l = l0 ∧ oldVariant = 0 then none else some (vf (10+l.index)) }
  values := fun p => if p = pkg 0 then some (.sum (value oldVariant oldDeps))
    else if p = pkg 1 then some (.sum (value 1 rightDeps))
    else if p = pkg 2 then some (.sum (value newVariant newDeps))
    else if p = pkg 3 then some (.payload ⟨33,externalDeps⟩ true)
    else if p = pkg 4 then some (.payload ⟨44,payloadDeps⟩ cap) else none
  loosePackages := {pkg 2,pkg 3,pkg 4}
  types := fun _ => sumType cap
  liveDomains := {⟨0⟩}
  domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
  usedValueFacts := {vf 0,vf 1,vf 10,vf 11}
  usedIncarnations := {⟨0⟩,⟨1⟩}
  usedOccurrences := {occ 0,occ 1,occ 9}

private def alloc (n variant : Nat) : Allocation :=
  ⟨vf (100+n),if variant = 0 then none else some (vf (110+n),occ (100+n))⟩
private def independent : State := fixture 1 1 true ∅ ∅ ∅ ∅ ∅
private def selfDependent : State := fixture 1 1 true {.occurrence (occ 0)} ∅ ∅ ∅ ∅
private def cyclic : State := fixture 1 1 false {.occurrence (occ 1)} {.occurrence (occ 0)} ∅ ∅ ∅

private theorem fixture_frame (ov nv : Nat) (cap : Bool) (d0 d1 dn dq dp : Finset Fact) :
    FrameWellFormed (fixture ov nv cap d0 d1 dn dq dp) := by
  constructor
  · intro l lt m mt same; exact congrArg (fun p : PlaceId => RootLocationId.mk p.index) same
  · intro l lt m mt same; exact congrArg (fun p : IncarnationId => RootLocationId.mk p.index) same
  · intro l lt m mt same; exact congrArg (fun p : ValueFactId => RootLocationId.mk p.index) same
  · intro l lt m mt same; exact congrArg (fun p : PackageId => RootLocationId.mk p.index) same
  · intro l lt; have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl <;> simp [fixture,pkg,l0,l1]
  · intro l _; simp [fixture]
  · intro l lt; have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl <;> simp [fixture,vf,l0,l1]
  · intro l lt; have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl <;> simp [fixture,l0,l1]
  · intro d; by_cases same : d = ⟨0⟩ <;> simp [fixture,same]

/-- Fixture checks are separate from DependenciesValid, enabling broken-rule tests. -/
private theorem fixture_shape (ov nv : Nat) (cap : Bool) (d0 d1 dn dq dp : Finset Fact)
    (ovAllowed : ov = 0 ∨ ov = 1 ∨ ov = 2) (nvAllowed : nv = 0 ∨ nv = 1 ∨ nv = 2)
    (deps : DependenciesValid (fixture ov nv cap d0 d1 dn dq dp)) :
    WellFormed (fixture ov nv cap d0 d1 dn dq dp) := by
  refine ⟨?_,deps⟩
  refine ⟨fixture_frame _ _ _ _ _ _ _ _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p carrier
    rcases carrier with loose|⟨l,lt,rfl⟩
    · have cases : p = pkg 2 ∨ p = pkg 3 ∨ p = pkg 4 := by simpa [fixture] using loose
      rcases cases with rfl|rfl|rfl <;> simp [fixture,pkg]
    · have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
      rcases cases with rfl|rfl <;> simp [fixture,pkg,l0,l1]
  · intro p carrier v data
    rcases carrier with loose|⟨l,lt,rfl⟩
    · have cases : p = pkg 2 ∨ p = pkg 3 ∨ p = pkg 4 := by simpa [fixture] using loose
      rcases cases with rfl|rfl|rfl
      · have same : v = value nv dn := by simpa [sumAt,fixture,pkg,SemanticValue.sumValue] using data.symm
        subst v; rcases nvAllowed with rfl|rfl|rfl <;> simp [ValueTyped,value,fixture,sumType,nominal]
      · simp [sumAt,fixture,pkg,SemanticValue.sumValue] at data
      · simp [sumAt,fixture,pkg,SemanticValue.sumValue] at data
    · have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
      rcases cases with rfl|rfl
      · have same : v = value ov d0 := by simpa [sumAt,fixture,pkg,l0,SemanticValue.sumValue] using data.symm
        subst v; rcases ovAllowed with rfl|rfl|rfl <;> simp [ValueTyped,value,fixture,sumType,nominal]
      · have same : v = value 1 d1 := by simpa [sumAt,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
        subst v; simp [ValueTyped,value,fixture,sumType,nominal]
  · intro l lt v data
    have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl <;> simpa [sumAt,fixture,pkg,l0,l1,SemanticValue.sumValue,value] using congrArg (Option.map SumValue.typeId) data.symm
  · intro l lt
    have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl <;> simp [fixture,pkg,l0,l1]
  · intro l lt v data
    have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl
    · have same : v = value ov d0 := by simpa [sumAt,fixture,pkg,l0,SemanticValue.sumValue] using data.symm
      subst v; by_cases empty : ov = 0 <;> simp [fixture,l0,value,empty]
    · have same : v = value 1 d1 := by simpa [sumAt,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
      subst v; simp [fixture,l0,l1,value]
  · intro l lt m mt o le me
    have lc : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    · rfl
    · by_cases empty : ov = 0
      · simp [fixture,l0,l1,empty] at le me
      · have le' : occ 0 = o := by simpa [fixture,l0,l1,empty] using le
        have me' : occ 1 = o := by simpa [fixture,l0,l1,empty] using me
        have impossible := congrArg OccurrenceId.index (le'.trans me'.symm)
        cases impossible
    · by_cases empty : ov = 0
      · simp [fixture,l0,l1,empty] at le me
      · have le' : occ 1 = o := by simpa [fixture,l0,l1,empty] using le
        have me' : occ 0 = o := by simpa [fixture,l0,l1,empty] using me
        have impossible := congrArg OccurrenceId.index (me'.trans le'.symm)
        cases impossible
    · rfl
  · intro l lt o active
    have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl
    · by_cases empty : ov = 0 <;> simp_all [fixture,l0,occ]
    · simp_all [fixture,l0,l1,occ]
  · intro l lt fact active
    have cases : l = l0 ∨ l = l1 := by simpa [fixture] using lt
    rcases cases with rfl|rfl
    · by_cases empty : ov = 0 <;> simp_all [fixture,l0,vf]
    · simp_all [fixture,l0,l1,vf]

private theorem fixture_dependencies (ov nv : Nat) (cap : Bool)
    (d0 d1 dn dq dp : Finset Fact)
    (oldLive : ∀ f ∈ d0, f ∈ LiveFacts (fixture ov nv cap d0 d1 dn dq dp))
    (rightLive : ∀ f ∈ d1, f ∈ LiveFacts (fixture ov nv cap d0 d1 dn dq dp))
    (newLive : ∀ f ∈ dn, f ∈ LiveFacts (fixture ov nv cap d0 d1 dn dq dp))
    (externalLive : ∀ f ∈ dq, f ∈ LiveFacts (fixture ov nv cap d0 d1 dn dq dp))
    (payloadLive : ∀ f ∈ dp, f ∈ LiveFacts (fixture ov nv cap d0 d1 dn dq dp)) :
    DependenciesValid (fixture ov nv cap d0 d1 dn dq dp) := by
  intro p carrier v data f dep
  simp only [fixture] at data
  split at data
  · cases data; by_cases empty : ov = 0
    · simp [SemanticValue.dependencies,SumValue.dependencies,value,empty] at dep
    · exact oldLive f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value,empty] using dep)
  · split at data
    · cases data; exact rightLive f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value] using dep)
    · split at data
      · cases data; by_cases empty : nv = 0
        · simp [SemanticValue.dependencies,SumValue.dependencies,value,empty] at dep
        · exact newLive f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value,empty] using dep)
      · split at data
        · cases data; exact externalLive f dep
        · split at data
          · cases data; exact payloadLive f dep
          · cases data

private theorem independent_wf : WellFormed independent := by
  apply fixture_shape 1 1 true ∅ ∅ ∅ ∅ ∅ (by simp) (by simp)
  apply fixture_dependencies <;> simp

private theorem self_wf : WellFormed selfDependent := by
  apply fixture_shape 1 1 true _ ∅ ∅ ∅ ∅ (by simp) (by simp)
  apply fixture_dependencies
  · intro f dep; have same : f = .occurrence (occ 0) := Finset.mem_singleton.mp dep
    subst f; exact ⟨l0,by simp [fixture],by simp [fixture,l0]⟩
  all_goals simp

private theorem cyclic_wf : WellFormed cyclic := by
  apply fixture_shape 1 1 false _ _ ∅ ∅ ∅ (by simp) (by simp)
  apply fixture_dependencies
  · intro f dep; have same : f = .occurrence (occ 1) := Finset.mem_singleton.mp dep
    subst f; exact ⟨l1,by simp [fixture],by simp [fixture,l0,l1]⟩
  · intro f dep; have same : f = .occurrence (occ 0) := Finset.mem_singleton.mp dep
    subst f; exact ⟨l0,by simp [fixture],by simp [fixture,l0]⟩
  all_goals simp

private theorem whole_raw (ov nv : Nat) (cap : Bool) (d0 d1 dn dq dp : Finset Fact)
    (ret : Bool) (discard : ret = false → cap = true) :
    RawWhole True True (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2)
      (value nv dn) (alloc 0 nv) ret (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret) := by
  constructor
  · simp [fixture]
  · simp [fixture]
  · simp [fixture,pkg]
  · rfl
  · constructor
    · simp [fixture,alloc,vf]
    · intro fact o eq
      by_cases empty : nv = 0
      · simp [alloc,empty] at eq
      · have same : fact = vf 110 ∧ o = occ 100 := by simpa [alloc,empty] using eq.symm
        rcases same with ⟨rfl,rfl⟩; simp [FreshOccurrence,fixture,vf,occ,alloc]
  · by_cases empty : nv = 0 <;> simp [FitsAllocation,alloc,value,empty]
  · intro noResult
    have enabled := discard noResult
    simp [fixture,sumType,SumType.discardable,enabled]
  · trivial
  · trivial
  · rfl

/-- The fixture's candidate structural checks do not assume dependency legality. -/
private theorem whole_frame (ov nv : Nat) (cap ret : Bool) (d0 d1 dn dq dp : Finset Fact) :
    FrameWellFormed (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret) := by
  have pre := fixture_frame ov nv cap d0 d1 dn dq dp
  constructor
  · intro l lt m mt same
    have le : ((wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret).root l).place = ⟨l.index⟩ := by
      by_cases eq : l = l0 <;> simp [wholeCandidate,installRoot,fixture,eq]
    have me : ((wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret).root m).place = ⟨m.index⟩ := by
      by_cases eq : m = l0 <;> simp [wholeCandidate,installRoot,fixture,eq]
    rw [le,me] at same; exact congrArg (fun p : PlaceId => RootLocationId.mk p.index) same
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [wholeCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [wholeCandidate,installRoot,fixture,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [wholeCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [wholeCandidate,installRoot,fixture,alloc,vf,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [wholeCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [wholeCandidate,installRoot,fixture,pkg,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> cases ret <;> simp [wholeCandidate,installRoot,fixture,pkg,l0,l1]
  · intro l lt; by_cases eq : l = l0 <;> simp [wholeCandidate,installRoot,fixture,eq]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [wholeCandidate,installRoot,fixture,alloc,Allocation.facts,vf,l0,l1]
  · intro l lt; by_cases same : l = l0 <;> simpa [wholeCandidate,installRoot,same] using pre.incarnationsRecorded l lt
  · exact pre.domainCarrierCoherent

private theorem whole_post_invariant (ov nv : Nat) (cap ret : Bool) (d0 d1 dn dq dp : Finset Fact)
    (pre : WellFormed (fixture ov nv cap d0 d1 dn dq dp))
    :
    Invariant (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret) := by
  let s := fixture ov nv cap d0 d1 dn dq dp
  let post := wholeCandidate s l0 (pkg 2) (alloc 0 nv) ret
  have prior : ∀ p, Survives post p → Survives s p := by
    intro p carrier
    rcases carrier with loose|⟨l,lt,eq⟩
    · cases ret
      · exact Or.inl (Finset.mem_erase.mp loose).2
      · rcases Finset.mem_insert.mp loose with old|prior
        · exact Or.inr ⟨l0,by simp [s,fixture],by simpa [s,fixture,l0,pkg] using old.symm⟩
        · exact Or.inl (Finset.mem_erase.mp prior).2
    · by_cases same : l = l0
      · subst l
        have incoming : p = pkg 2 := by simpa [post,wholeCandidate,installRoot] using eq.symm
        exact Or.inl (incoming ▸ (by simp [s,fixture]))
      · exact Or.inr ⟨l,lt,by simpa [post,wholeCandidate,same] using eq⟩
  refine ⟨whole_frame _ _ _ _ _ _ _ _ _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p carrier; exact pre.present p (prior p carrier)
  · intro p carrier v data; exact pre.typed p (prior p carrier) v data
  · intro l lt v data
    by_cases same : l = l0
    · subst l
      have vEq : v = value nv dn := by simpa [sumAt,wholeCandidate,installRoot,fixture,pkg,SemanticValue.sumValue] using data.symm
      subst v; rfl
    · have priorData : sumAt s (s.root l).package = some v := by
        simpa [s,sumAt,wholeCandidate,same] using data
      have typeEq := pre.installedType l lt v priorData
      simpa [wholeCandidate,same] using typeEq
  · intro l lt; by_cases same : l = l0
    · subst l; simp [wholeCandidate,installRoot,fixture,pkg]
    · simpa [wholeCandidate,same] using pre.installedSum l lt
  · intro l lt v data
    by_cases same : l = l0
    · subst l
      have vEq : v = value nv dn := by simpa [sumAt,wholeCandidate,installRoot,fixture,pkg,SemanticValue.sumValue] using data.symm
      subst v; by_cases empty : nv = 0 <;> simp [wholeCandidate,installRoot,alloc,value,empty]
    · have priorData : sumAt s (s.root l).package = some v := by simpa [s,sumAt,wholeCandidate,same] using data
      simpa [wholeCandidate,same] using pre.occurrenceShape l lt v priorData
  · intro l lt m mt o le me
    have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [wholeCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    · rfl
    · by_cases empty : nv = 0
      · simp [wholeCandidate,installRoot,alloc,empty] at le
      · have oe : o = occ 100 := by simpa [wholeCandidate,installRoot,alloc,empty] using le.symm
        subst o; simp [wholeCandidate,fixture,l0,l1,occ] at me
    · by_cases empty : nv = 0
      · simp [wholeCandidate,installRoot,alloc,empty] at me
      · have oe : o = occ 100 := by simpa [wholeCandidate,installRoot,alloc,empty] using me.symm
        subst o; simp [wholeCandidate,fixture,l0,l1,occ] at le
    · rfl
  · intro l lt o active; by_cases same : l = l0
    · subst l; by_cases empty : nv = 0
      · simp [wholeCandidate,installRoot,alloc,empty] at active
      · have oe : o = occ 100 := by simpa [wholeCandidate,installRoot,alloc,empty] using active.symm
        subst o; simp [wholeCandidate,alloc,Allocation.occurrences,empty]
    · have old : (s.root l).occurrence = some o := by simpa [s,wholeCandidate,same] using active
      exact Finset.mem_union_left _ (pre.occurrencesRecorded l lt o old)
  · intro l lt fact active; by_cases same : l = l0
    · subst l; by_cases empty : nv = 0
      · simp [wholeCandidate,installRoot,alloc,empty] at active
      · have fe : fact = vf 110 := by simpa [wholeCandidate,installRoot,alloc,empty] using active.symm
        subst fact; simp [wholeCandidate,alloc,Allocation.facts,empty]
    · have old : (s.root l).payloadFact = some fact := by simpa [s,wholeCandidate,same] using active
      exact Finset.mem_union_left _ (pre.payloadFactsRecorded l lt fact old)

private theorem whole_post_wf (ov nv : Nat) (cap ret : Bool) (d0 d1 dn dq dp : Finset Fact)
    (pre : WellFormed (fixture ov nv cap d0 d1 dn dq dp))
    (deps : DependenciesValid (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret)) :
    WellFormed (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret) :=
  ⟨whole_post_invariant _ _ _ _ _ _ _ _ _ pre,deps⟩

private theorem whole_dependencies (ov nv : Nat) (cap ret : Bool) (d0 d1 dn dq dp : Finset Fact)
    (oldLive : ret = true → ∀ f ∈ d0, f ∈ LiveFacts (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret))
    (rightLive : ∀ f ∈ d1, f ∈ LiveFacts (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret))
    (newLive : ∀ f ∈ dn, f ∈ LiveFacts (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret))
    (externalLive : ∀ f ∈ dq, f ∈ LiveFacts (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret))
    (payloadLive : ∀ f ∈ dp, f ∈ LiveFacts (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret)) :
    DependenciesValid (wholeCandidate (fixture ov nv cap d0 d1 dn dq dp) l0 (pkg 2) (alloc 0 nv) ret) := by
  intro p carrier v data f dep
  simp only [wholeCandidate,fixture] at data
  split at data
  · rename_i same
    cases data
    have mustReturn : ret = true := by
      cases ret
      · rcases carrier with loose|⟨l,lt,eq⟩
        · have choices : p = pkg 3 ∨ p = pkg 4 := by simpa [wholeCandidate,fixture,pkg] using loose
          rcases choices with rfl|rfl <;> simp [pkg] at same
        · have lc : l = l0 ∨ l = l1 := by simpa [wholeCandidate,fixture] using lt
          rcases lc with rfl|rfl <;> simp_all [wholeCandidate,installRoot,fixture,pkg,l0,l1]
      · rfl
    by_cases empty : ov = 0
    · simp [SemanticValue.dependencies,SumValue.dependencies,value,empty] at dep
    · exact oldLive mustReturn f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value,empty] using dep)
  · split at data
    · cases data; exact rightLive f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value] using dep)
    · split at data
      · cases data; by_cases empty : nv = 0
        · simp [SemanticValue.dependencies,SumValue.dependencies,value,empty] at dep
        · exact newLive f (by simpa [SemanticValue.dependencies,SumValue.dependencies,value,empty] using dep)
      · split at data
        · cases data; exact externalLive f dep
        · split at data
          · cases data; exact payloadLive f dep
          · cases data

private theorem independent_variant_replace (ov nv : Nat)
    (oa : ov = 0 ∨ ov = 1 ∨ ov = 2) (na : nv = 0 ∨ nv = 1 ∨ nv = 2) :
    WholeReplaceStep True True (fixture ov nv true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2)
      (value nv ∅) (alloc 0 nv) (wholeCandidate (fixture ov nv true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2) (alloc 0 nv) true) := by
  have pre : WellFormed (fixture ov nv true ∅ ∅ ∅ ∅ ∅) := by
    apply fixture_shape _ _ _ _ _ _ _ _ oa na
    apply fixture_dependencies <;> simp
  exact ⟨pre,whole_raw _ _ _ _ _ _ _ _ _ (by simp),whole_post_wf _ _ _ _ _ _ _ _ _ pre
    (by apply whole_dependencies <;> simp)⟩

theorem none_to_some_is_legal :
    WholeReplaceStep True True (fixture 0 1 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2)
      (value 1 ∅) (alloc 0 1) (wholeCandidate (fixture 0 1 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2) (alloc 0 1) true) := independent_variant_replace 0 1 (by simp) (by simp)
theorem some_to_none_is_legal :
    WholeReplaceStep True True (fixture 1 0 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2)
      (value 0 ∅) (alloc 0 0) (wholeCandidate (fixture 1 0 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2) (alloc 0 0) true) := independent_variant_replace 1 0 (by simp) (by simp)
theorem some_to_same_variant_is_legal :
    WholeReplaceStep True True (fixture 1 1 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2)
      (value 1 ∅) (alloc 0 1) (wholeCandidate (fixture 1 1 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2) (alloc 0 1) true) := independent_variant_replace 1 1 (by simp) (by simp)
theorem different_payload_variants_is_legal :
    WholeReplaceStep True True (fixture 1 2 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2)
      (value 2 ∅) (alloc 0 2) (wholeCandidate (fixture 1 2 true ∅ ∅ ∅ ∅ ∅) l0 (pkg 2) (alloc 0 2) true) := independent_variant_replace 1 2 (by simp) (by simp)

theorem independent_whole_replace_is_legal :
    WholeReplaceStep True True independent l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate independent l0 (pkg 2) (alloc 0 1) true) := some_to_same_variant_is_legal

theorem same_variant_whole_replace_restarts_occurrence :
    ((wholeCandidate independent l0 (pkg 2) (alloc 0 1) true).root l0).occurrence = some (occ 100) := by
  simp [wholeCandidate,installRoot,alloc]

theorem whole_store_eliminates_old_only_occurrence_dependency :
    WholeStoreStep True True selfDependent l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate selfDependent l0 (pkg 2) (alloc 0 1) false) := by
  exact ⟨self_wf,whole_raw _ _ _ _ _ _ _ _ _ (by simp),whole_post_wf _ _ _ _ _ _ _ _ _ self_wf
    (by apply whole_dependencies <;> simp)⟩

theorem whole_replace_rejects_old_only_occurrence_dependency :
    ¬ WholeReplaceStep True True selfDependent l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate selfDependent l0 (pkg 2) (alloc 0 1) true) := by
  exact whole_replace_rejects_returned_occurrence_dependency
    (o := occ 0) (value := .sum (value 1 {.occurrence (occ 0)}))
    (by simp [selfDependent,fixture,l0]) (by simp [selfDependent,fixture,pkg,l0])
    (by simp [SemanticValue.dependencies,SumValue.dependencies,value])

theorem occurrence_dependency_rejects_replace_but_allows_store :
    ¬ WholeReplaceStep True True selfDependent l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate selfDependent l0 (pkg 2) (alloc 0 1) true) ∧
    WholeStoreStep True True selfDependent l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate selfDependent l0 (pkg 2) (alloc 0 1) false) :=
  ⟨whole_replace_rejects_old_only_occurrence_dependency,whole_store_eliminates_old_only_occurrence_dependency⟩

theorem same_place_sum_swap_is_exact_noop : SwapStep True True selfDependent l0 l0 selfDependent :=
  ⟨self_wf,RawSwap.same (by simp [selfDependent,fixture]) trivial trivial,self_wf⟩

theorem same_place_sum_swap_self_dependency_remains_live :
    SwapStep True True selfDependent l0 l0 selfDependent ∧
    Fact.occurrence (occ 0) ∈ LiveFacts selfDependent :=
  ⟨same_place_sum_swap_is_exact_noop,⟨l0,by simp [selfDependent,fixture],by simp [selfDependent,fixture,l0]⟩⟩

private def withIncomingDependency : State := fixture 1 1 true ∅ ∅ {.occurrence (occ 0)} ∅ ∅
private def withExternalDependency : State := fixture 1 1 true ∅ ∅ ∅ {.occurrence (occ 0)} ∅

theorem whole_incoming_occurrence_dependency_rejects_replace_and_store :
    (∀ ret post, ¬ WholeStep True True withIncomingDependency l0 (pkg 2)
      (value 1 {.occurrence (occ 0)}) (alloc 0 1) ret post) := by
  intro ret post
  apply whole_rejects_incoming_occurrence_dependency (o := occ 0)
  · simp [withIncomingDependency,fixture,l0]
  · simp [SumValue.dependencies,value]

theorem whole_external_occurrence_dependency_rejects_replace_and_store :
    ∀ ret post, ¬ WholeStep True True withExternalDependency l0 (pkg 2)
      (value 1 ∅) (alloc 0 1) ret post := by
  intro ret post step
  have raw := step.2.1
  apply whole_rejects_ended_occurrence_in_survivor (pkg := pkg 3) (value := .payload ⟨33,{.occurrence (occ 0)}⟩ true)
    step.1 raw (o := occ 0) (by simp [withExternalDependency,fixture,l0]) ?_ ?_ (by simp [SemanticValue.dependencies]) step.2.2
  · apply Or.inl
    rw [raw.post_eq]; cases ret <;> simp [wholeCandidate,withExternalDependency,fixture,pkg,l0]
  · rw [(whole_preserves_static_frame raw).2.2.2.2.2]
    simp [withExternalDependency,fixture,pkg]

theorem historically_used_but_dead_occurrence_is_not_fresh :
    Fact.occurrence (occ 9) ∉ LiveFacts independent ∧ ¬ FreshOccurrence independent (occ 9) := by
  constructor
  · intro live; rcases live with ⟨l,lt,active⟩
    have choices : l = l0 ∨ l = l1 := by simpa [independent,fixture] using lt
    rcases choices with rfl|rfl <;> simp [independent,fixture,l0,l1,occ] at active
  · simp [FreshOccurrence,independent,fixture]

theorem historical_occurrence_reuse_rejected :
    ¬ FreshAllocation independent ⟨vf 100,some (vf 110,occ 9)⟩ := by
  intro fresh
  exact fresh_allocation_cannot_reuse_occurrence fresh rfl (by simp [independent,fixture])

/-- A tempting variant-specific guard would allow None, but the nominal type's
other possible variant is non-Discardable. The actual whole-store guard rejects. -/
private def nonDiscardableNone : State := fixture 0 1 false ∅ ∅ ∅ ∅ ∅
theorem current_variant_discardability_is_an_unsound_store_guard :
    (nonDiscardableNone.types nominal).hasPayload ⟨0⟩ = false ∧
    (nonDiscardableNone.types nominal).discardable = false ∧
    ¬ WholeStoreStep True True nonDiscardableNone l0 (pkg 2) (value 1 ∅) (alloc 0 1)
      (wholeCandidate nonDiscardableNone l0 (pkg 2) (alloc 0 1) false) := by
  refine ⟨rfl,by simp [nonDiscardableNone,fixture,sumType,SumType.discardable],?_⟩
  apply whole_store_rejects_nonDiscardable_sum
  simp [nonDiscardableNone,fixture,sumType,SumType.discardable]

private theorem swap_raw (cap : Bool) (d0 d1 dn dq dp : Finset Fact) :
    RawSwapDistinct True True (fixture 1 1 cap d0 d1 dn dq dp) l0 l1
      (value 1 d0) (value 1 d1) (alloc 0 1) (alloc 1 1)
      (swapCandidate (fixture 1 1 cap d0 d1 dn dq dp) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  constructor
  · simp [fixture]
  · simp [fixture]
  · decide
  · simp [fixture,pkg,l0]
  · simp [fixture,pkg,l1]
  · rfl
  · refine ⟨?_,?_,?_,?_⟩
    · constructor
      · simp [fixture,alloc,vf]
      · intro v o eq
        have same : v = vf 110 ∧ o = occ 100 := by simpa [alloc] using eq.symm
        rcases same with ⟨rfl,rfl⟩; simp [fixture,FreshOccurrence,vf,occ,alloc]
    · constructor
      · simp [fixture,alloc,vf]
      · intro v o eq
        have same : v = vf 111 ∧ o = occ 101 := by simpa [alloc] using eq.symm
        rcases same with ⟨rfl,rfl⟩; simp [fixture,FreshOccurrence,vf,occ,alloc]
    · simp [Allocation.facts,alloc,vf,Finset.disjoint_left]
    · simp [Allocation.occurrences,alloc,occ]
  · simp [FitsAllocation,alloc,value]
  · simp [FitsAllocation,alloc,value]
  · trivial
  · trivial
  · rfl

private theorem swap_frame (cap : Bool) (d0 d1 dn dq dp : Finset Fact) :
    FrameWellFormed (swapCandidate (fixture 1 1 cap d0 d1 dn dq dp) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  constructor
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [swapCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [swapCandidate,installRoot,fixture,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [swapCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [swapCandidate,installRoot,fixture,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [swapCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [swapCandidate,installRoot,alloc,vf,l0,l1]
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [swapCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl <;> simp_all [swapCandidate,installRoot,fixture,pkg,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [swapCandidate,installRoot,fixture,pkg,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [swapCandidate,installRoot,fixture,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [swapCandidate,installRoot,fixture,alloc,Allocation.facts,vf,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [swapCandidate,installRoot,fixture,l0,l1]
  · exact (fixture_frame 1 1 cap d0 d1 dn dq dp).domainCarrierCoherent

private theorem swap_post_invariant (cap : Bool) (d0 d1 dn dq dp : Finset Fact)
    (pre : WellFormed (fixture 1 1 cap d0 d1 dn dq dp))
    :
    Invariant (swapCandidate (fixture 1 1 cap d0 d1 dn dq dp) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  let s := fixture 1 1 cap d0 d1 dn dq dp
  let post := swapCandidate s l0 l1 (alloc 0 1) (alloc 1 1)
  have raw := swap_raw cap d0 d1 dn dq dp
  have prior : ∀ p, Survives post p → Survives s p := by
    intro p carrier
    rcases carrier with loose|⟨l,lt,eq⟩
    · exact Or.inl loose
    · have lc : l = l0 ∨ l = l1 := by simpa [post,s,swapCandidate,fixture] using lt
      rcases lc with rfl|rfl
      · exact Or.inr ⟨l1,by simp [s,fixture],by simpa [post,swapCandidate,installRoot] using eq⟩
      · exact Or.inr ⟨l0,by simp [s,fixture],by simpa [post,swapCandidate,installRoot,l0,l1] using eq⟩
  refine ⟨swap_frame _ _ _ _ _ _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p carrier; exact pre.present p (prior p carrier)
  · intro p carrier v data; exact pre.typed p (prior p carrier) v data
  · intro l lt v data
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl
    · have ve : v = value 1 d1 := by simpa [sumAt,swapCandidate,installRoot,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
      subst v; rfl
    · have ve : v = value 1 d0 := by simpa [sumAt,swapCandidate,installRoot,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
      subst v; rfl
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl <;> simp [swapCandidate,installRoot,fixture,pkg,l0,l1]
  · intro l lt v data
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl
    · have ve : v = value 1 d1 := by simpa [sumAt,swapCandidate,installRoot,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
      subst v; simp [swapCandidate,installRoot,alloc,value,l0,l1]
    · have ve : v = value 1 d0 := by simpa [sumAt,swapCandidate,installRoot,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
      subst v; simp [swapCandidate,installRoot,alloc,value,l0,l1]
  · intro l lt m mt o le me
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [swapCandidate,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    · rfl
    · have oe : o = occ 100 := by simpa [swapCandidate,installRoot,alloc] using le.symm
      subst o; simp [swapCandidate,installRoot,alloc,l0,l1,occ] at me
    · have oe : o = occ 101 := by simpa [swapCandidate,installRoot,alloc,l0,l1] using le.symm
      subst o; simp [swapCandidate,installRoot,alloc,occ] at me
    · rfl
  · intro l lt o active
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl
    · have oe : o = occ 100 := by simpa [swapCandidate,installRoot,alloc] using active.symm
      subst o; simp [swapCandidate,alloc,Allocation.occurrences]
    · have oe : o = occ 101 := by simpa [swapCandidate,installRoot,alloc,l0,l1] using active.symm
      subst o; simp [swapCandidate,alloc,Allocation.occurrences]
  · intro l lt fact active
    have lc : l = l0 ∨ l = l1 := by simpa [swapCandidate,fixture] using lt
    rcases lc with rfl|rfl
    · have fe : fact = vf 110 := by simpa [swapCandidate,installRoot,alloc] using active.symm
      subst fact; simp [swapCandidate,alloc,Allocation.facts]
    · have fe : fact = vf 111 := by simpa [swapCandidate,installRoot,alloc,l0,l1] using active.symm
      subst fact; simp [swapCandidate,alloc,Allocation.facts]

private theorem swap_post_wf (cap : Bool) (d0 d1 dn dq dp : Finset Fact)
    (pre : WellFormed (fixture 1 1 cap d0 d1 dn dq dp))
    (deps : DependenciesValid (swapCandidate (fixture 1 1 cap d0 d1 dn dq dp) l0 l1 (alloc 0 1) (alloc 1 1))) :
    WellFormed (swapCandidate (fixture 1 1 cap d0 d1 dn dq dp) l0 l1 (alloc 0 1) (alloc 1 1)) :=
  ⟨swap_post_invariant _ _ _ _ _ _ pre,deps⟩

private theorem empty_swap_dependencies (cap : Bool) :
    DependenciesValid (swapCandidate (fixture 1 1 cap ∅ ∅ ∅ ∅ ∅) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro p carrier v data f dep
  have eqData : (fixture 1 1 cap ∅ ∅ ∅ ∅ ∅).values p = some v := data
  simp only [fixture] at eqData
  split at eqData
  · cases eqData; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
  · split at eqData
    · cases eqData; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
    · split at eqData
      · cases eqData; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
      · split at eqData
        · cases eqData; exact False.elim (Finset.notMem_empty _ dep)
        · split at eqData
          · cases eqData; exact False.elim (Finset.notMem_empty _ dep)
          · cases eqData

theorem independent_distinct_sum_swap_is_legal :
    SwapStep True True independent l0 l1 (swapCandidate independent l0 l1 (alloc 0 1) (alloc 1 1)) :=
  ⟨independent_wf,RawSwap.distinct (swap_raw _ _ _ _ _ _),swap_post_wf _ _ _ _ _ _ independent_wf (empty_swap_dependencies true)⟩

theorem nonDiscardable_sum_values_can_swap :
    SwapStep True True (fixture 1 1 false ∅ ∅ ∅ ∅ ∅) l0 l1
      (swapCandidate (fixture 1 1 false ∅ ∅ ∅ ∅ ∅) l0 l1 (alloc 0 1) (alloc 1 1)) ∧
    (sumType false).discardable = false := by
  have pre : WellFormed (fixture 1 1 false ∅ ∅ ∅ ∅ ∅) := by
    apply fixture_shape _ _ _ _ _ _ _ _ (by simp) (by simp)
    apply fixture_dependencies <;> simp
  exact ⟨⟨pre,RawSwap.distinct (swap_raw _ _ _ _ _ _),swap_post_wf _ _ _ _ _ _ pre (empty_swap_dependencies false)⟩,
    by simp [sumType,SumType.discardable]⟩

theorem cyclic_swap_occurrence_laundering_rejected :
    ¬ SwapStep True True cyclic l0 l1 (swapCandidate cyclic l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro step
  exact swap_rejects_left_package_occurrence_dependency cyclic_wf (swap_raw _ _ _ _ _ _)
    (o := occ 1) (Or.inr (by simp [cyclic,fixture,l0,l1]))
    (by simp [SumValue.dependencies,value]) step.2.2

theorem self_dependency_allows_same_swap_but_rejects_distinct :
    SwapStep True True selfDependent l0 l0 selfDependent ∧
    ¬ SwapStep True True selfDependent l0 l1 (swapCandidate selfDependent l0 l1 (alloc 0 1) (alloc 1 1)) := by
  refine ⟨same_place_sum_swap_is_exact_noop,?_⟩
  intro step
  exact swap_rejects_left_package_occurrence_dependency self_wf (swap_raw _ _ _ _ _ _)
    (o := occ 0) (Or.inl (by simp [selfDependent,fixture,l0]))
    (by simp [SumValue.dependencies,value]) step.2.2

private def allowedOccurrences : Finset Fact := {.occurrence (occ 0),.occurrence (occ 1)}
private theorem occurrence_fixture_wf (cap : Bool) (d0 d1 dn dq dp : Finset Fact)
    (a0 : d0 ⊆ allowedOccurrences) (a1 : d1 ⊆ allowedOccurrences)
    (an : dn ⊆ allowedOccurrences) (aq : dq ⊆ allowedOccurrences) (ap : dp ⊆ allowedOccurrences) :
    WellFormed (fixture 1 1 cap d0 d1 dn dq dp) := by
  have live : ∀ f ∈ allowedOccurrences, f ∈ LiveFacts (fixture 1 1 cap d0 d1 dn dq dp) := by
    intro f dep
    have cases : f = .occurrence (occ 0) ∨ f = .occurrence (occ 1) := by simpa [allowedOccurrences] using dep
    rcases cases with rfl|rfl
    · exact ⟨l0,by simp [fixture],by simp [fixture,l0]⟩
    · exact ⟨l1,by simp [fixture],by simp [fixture,l0,l1]⟩
  apply fixture_shape _ _ _ _ _ _ _ _ (by simp) (by simp)
  exact fixture_dependencies _ _ _ _ _ _ _ _ (fun f d=>live f (a0 d)) (fun f d=>live f (a1 d))
    (fun f d=>live f (an d)) (fun f d=>live f (aq d)) (fun f d=>live f (ap d))

theorem left_cross_occurrence_swap_dependency_rejected :
    ¬ SwapStep True True (fixture 1 1 true {.occurrence (occ 1)} ∅ ∅ ∅ ∅) l0 l1
      (swapCandidate (fixture 1 1 true {.occurrence (occ 1)} ∅ ∅ ∅ ∅) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro step
  exact swap_rejects_left_package_occurrence_dependency step.1 (swap_raw _ _ _ _ _ _)
    (o := occ 1) (Or.inr (by simp [fixture,l0,l1])) (by simp [SumValue.dependencies,value]) step.2.2

theorem right_self_occurrence_swap_dependency_rejected :
    ¬ SwapStep True True (fixture 1 1 true ∅ {.occurrence (occ 1)} ∅ ∅ ∅) l0 l1
      (swapCandidate (fixture 1 1 true ∅ {.occurrence (occ 1)} ∅ ∅ ∅) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro step
  exact swap_rejects_right_package_occurrence_dependency step.1 (swap_raw _ _ _ _ _ _)
    (o := occ 1) (Or.inr (by simp [fixture,l0,l1])) (by simp [SumValue.dependencies,value]) step.2.2

theorem right_cross_occurrence_swap_dependency_rejected :
    ¬ SwapStep True True (fixture 1 1 true ∅ {.occurrence (occ 0)} ∅ ∅ ∅) l0 l1
      (swapCandidate (fixture 1 1 true ∅ {.occurrence (occ 0)} ∅ ∅ ∅) l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro step
  exact swap_rejects_right_package_occurrence_dependency step.1 (swap_raw _ _ _ _ _ _)
    (o := occ 0) (Or.inl (by simp [fixture,l0])) (by simp [SumValue.dependencies,value]) step.2.2

theorem third_survivor_occurrence_swap_dependency_rejected :
    ¬ SwapStep True True withExternalDependency l0 l1
      (swapCandidate withExternalDependency l0 l1 (alloc 0 1) (alloc 1 1)) := by
  intro step
  apply swap_rejects_any_surviving_ended_occurrence (pkg := pkg 3)
    (value := .payload ⟨33,{.occurrence (occ 0)}⟩ true) step.1 (swap_raw _ _ _ _ _ _)
    (o := occ 0) (Or.inl (by simp [withExternalDependency,fixture,l0]))
    (Or.inl (by simp [swapCandidate,fixture]))
    (by simp [swapCandidate,fixture,pkg])
    (by simp [SemanticValue.dependencies]) step.2.2

theorem cyclic_candidate_passes_all_other_invariants_but_fails_dependencies :
    RawSwapDistinct True True cyclic l0 l1 (value 1 {.occurrence (occ 1)}) (value 1 {.occurrence (occ 0)})
      (alloc 0 1) (alloc 1 1) (swapCandidate cyclic l0 l1 (alloc 0 1) (alloc 1 1)) ∧
    Invariant (swapCandidate cyclic l0 l1 (alloc 0 1) (alloc 1 1)) ∧
    ¬ DependenciesValid (swapCandidate cyclic l0 l1 (alloc 0 1) (alloc 1 1)) := by
  refine ⟨swap_raw _ _ _ _ _ _,swap_post_invariant _ _ _ _ _ _ cyclic_wf,?_⟩
  intro deps
  have malformed := swap_rejects_left_package_occurrence_dependency cyclic_wf (swap_raw _ _ _ _ _ _)
    (o := occ 1) (Or.inr (by simp [cyclic,fixture,l0,l1])) (by simp [SumValue.dependencies,value])
  exact malformed ⟨swap_post_invariant _ _ _ _ _ _ cyclic_wf,deps⟩

private def payloadPost (ret : Bool) : State :=
  payloadCandidate selfDependent l0 (pkg 4) (pkg 5) (value 1 {.occurrence (occ 0)}) ⟨44,∅⟩ true (vf 100) (vf 110) ret

private theorem payload_raw (ret : Bool) :
    RawPayload True True selfDependent l0 (pkg 4) (pkg 5) (value 1 {.occurrence (occ 0)})
      ⟨44,∅⟩ true (vf 100) (vf 110) ret (payloadPost ret) := by
  constructor
  · simp [selfDependent,fixture]
  · simp [selfDependent,fixture,pkg,l0]
  · rfl
  · exact ⟨occ 0,by simp [selfDependent,fixture,l0]⟩
  · simp [selfDependent,fixture]
  · simp [selfDependent,fixture,pkg]
  · rfl
  · intro _ carrier
    rcases carrier with loose|⟨l,lt,same⟩
    · simp [selfDependent,fixture,pkg] at loose
    · have cases : l = l0 ∨ l = l1 := by simpa [selfDependent,fixture] using lt
      rcases cases with rfl|rfl <;> simp [selfDependent,fixture,pkg,l0,l1] at same
  · simp [selfDependent,fixture,vf]
  · simp [selfDependent,fixture,vf]
  · decide
  · simp
  · trivial
  · trivial
  · rfl

private theorem payload_frame (ret : Bool) : FrameWellFormed (payloadPost ret) := by
  have pre := self_wf.frame
  constructor
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    all_goals first | rfl | simp [payloadPost,payloadCandidate,selfDependent,fixture,l0,l1] at same
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    all_goals first | rfl | simp [payloadPost,payloadCandidate,selfDependent,fixture,l0,l1] at same
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    all_goals first | rfl | simp [payloadPost,payloadCandidate,selfDependent,fixture,vf,l0,l1] at same
  · intro l lt m mt same
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    have mc : m = l0 ∨ m = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using mt
    rcases lc with rfl|rfl <;> rcases mc with rfl|rfl
    all_goals first | rfl | simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1] at same
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    rcases lc with rfl|rfl <;> cases ret <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    rcases lc with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    rcases lc with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,vf,l0,l1]
  · intro l lt
    have lc : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
    rcases lc with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,l0,l1]
  · exact pre.domainCarrierCoherent

private theorem payload_loose_equation (ret : Bool) :
    (payloadPost ret).loosePackages = if ret then {pkg 5,pkg 2,pkg 3} else {pkg 2,pkg 3} := by
  cases ret <;> ext p
  all_goals
    by_cases four : p = pkg 4 <;> by_cases two : p = pkg 2 <;> by_cases three : p = pkg 3 <;>
      simp_all [payloadPost,payloadCandidate,selfDependent,fixture,pkg]

private theorem payload_post_wf (ret : Bool) : WellFormed (payloadPost ret) := by
  have raw := payload_raw ret
  have pre := self_wf
  refine ⟨?_,?_⟩
  · refine ⟨payload_frame ret,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro p carrier
      rcases carrier with loose|⟨l,lt,rfl⟩
      · cases ret
        · have cases : p = pkg 2 ∨ p = pkg 3 := by simpa [payload_loose_equation] using loose
          rcases cases with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,value]
        · have cases : p = pkg 5 ∨ p = pkg 2 ∨ p = pkg 3 := by simpa [payload_loose_equation] using loose
          rcases cases with rfl|rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,value]
      · have cases : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
        rcases cases with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1]
    · intro p carrier v data
      simp only [sumAt,payloadPost,payloadCandidate,selfDependent,fixture] at data
      split at data
      · have ve : v = {value 1 {.occurrence (occ 0)} with payload := some ⟨44,∅⟩} := by simpa [SemanticValue.sumValue] using data.symm
        subst v; simp [ValueTyped,payloadPost,payloadCandidate,selfDependent,fixture,value,sumType,nominal]
      · split at data
        · simp [value,SemanticValue.sumValue] at data
        · split at data
          · have ve : v = value 1 {.occurrence (occ 0)} := by simpa [SemanticValue.sumValue] using data.symm
            subst v; simp [ValueTyped,payloadPost,payloadCandidate,selfDependent,fixture,value,sumType,nominal]
          · split at data
            · have ve : v = value 1 ∅ := by simpa [SemanticValue.sumValue] using data.symm
              subst v; simp [ValueTyped,payloadPost,payloadCandidate,selfDependent,fixture,value,sumType,nominal]
            · split at data
              · have ve : v = value 1 ∅ := by simpa [SemanticValue.sumValue] using data.symm
                subst v; simp [ValueTyped,payloadPost,payloadCandidate,selfDependent,fixture,value,sumType,nominal]
              · split at data
                · simp [SemanticValue.sumValue] at data
                · split at data <;> simp [SemanticValue.sumValue] at data
    · intro l lt v data
      have cases : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
      rcases cases with rfl|rfl
      · have ve : v = {value 1 {.occurrence (occ 0)} with payload := some ⟨44,∅⟩} := by
          simpa [sumAt,payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,SemanticValue.sumValue] using data.symm
        subst v; rfl
      · have ve : v = value 1 ∅ := by
          simpa [sumAt,payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
        subst v; rfl
    · intro l lt
      have cases : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
      rcases cases with rfl|rfl <;> simp [payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1]
    · intro l lt v data
      have cases : l = l0 ∨ l = l1 := by simpa [payloadPost,payloadCandidate,selfDependent,fixture] using lt
      rcases cases with rfl|rfl
      · have ve : v = {value 1 {.occurrence (occ 0)} with payload := some ⟨44,∅⟩} := by
          simpa [sumAt,payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,SemanticValue.sumValue] using data.symm
        subst v; simp [payloadPost,payloadCandidate,selfDependent,fixture,value,l0]
      · have ve : v = value 1 ∅ := by
          simpa [sumAt,payloadPost,payloadCandidate,selfDependent,fixture,pkg,l0,l1,SemanticValue.sumValue] using data.symm
        subst v; simp [payloadPost,payloadCandidate,selfDependent,fixture,value,l0,l1]
    · intro l lt m mt o le me
      have oldLeft : (selfDependent.root l).occurrence = some o := by
        by_cases eq : l = l0 <;> simpa [payloadPost,payloadCandidate,eq] using le
      have oldRight : (selfDependent.root m).occurrence = some o := by
        by_cases eq : m = l0 <;> simpa [payloadPost,payloadCandidate,eq] using me
      exact pre.occurrencesUnique l lt m mt o oldLeft oldRight
    · intro l lt o active
      have old : (selfDependent.root l).occurrence = some o := by
        by_cases eq : l = l0 <;> simpa [payloadPost,payloadCandidate,eq] using active
      exact pre.occurrencesRecorded l lt o old
    · intro l lt fact active
      by_cases eq : l = l0
      · subst l; have fe : fact = vf 110 := by simpa [payloadPost,payloadCandidate] using active.symm
        subst fact; simp [payloadPost,payloadCandidate]
      · have old : (selfDependent.root l).payloadFact = some fact := by simpa [payloadPost,payloadCandidate,eq] using active
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (pre.payloadFactsRecorded l lt fact old))
  · intro p carrier v data f dep
    have live : Fact.occurrence (occ 0) ∈ LiveFacts (payloadPost ret) :=
      payload_occurrence_dependency_remains_live raw (by simp [selfDependent,fixture,l0])
    simp only [payloadPost,payloadCandidate,selfDependent,fixture] at data
    split at data
    · cases data; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
    · split at data
      · cases ret
        · rename_i condition; simp at condition
        · have ve : v = .payload ⟨11,{.occurrence (occ 0)}⟩ true := by simpa [value] using data.symm
          subst v
          have fe : f = .occurrence (occ 0) := Finset.mem_singleton.mp dep
          subst f; exact live
      · split at data
        · cases data
          have fe : f = .occurrence (occ 0) := by simpa [SemanticValue.dependencies,SumValue.dependencies,value] using dep
          subst f; exact live
        · split at data
          · cases data; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
          · split at data
            · cases data; simp [SemanticValue.dependencies,SumValue.dependencies,value] at dep
            · split at data
              · cases data; exact False.elim (Finset.notMem_empty _ dep)
              · split at data
                · cases data; exact False.elim (Finset.notMem_empty _ dep)
                · cases data

theorem payload_only_replace_preserves_occurrence_with_self_dependency :
    PayloadStep True True selfDependent l0 (pkg 4) (pkg 5) (value 1 {.occurrence (occ 0)})
      ⟨44,∅⟩ true (vf 100) (vf 110) true (payloadPost true) ∧
    ((payloadPost true).root l0).occurrence = some (occ 0) :=
  ⟨⟨self_wf,payload_raw true,payload_post_wf true⟩,by simp [payloadPost,payloadCandidate,selfDependent,fixture,l0]⟩

theorem payload_only_store_preserves_occurrence :
    PayloadStep True True selfDependent l0 (pkg 4) (pkg 5) (value 1 {.occurrence (occ 0)})
      ⟨44,∅⟩ true (vf 100) (vf 110) false (payloadPost false) ∧
    ((payloadPost false).root l0).occurrence = some (occ 0) :=
  ⟨⟨self_wf,payload_raw false,payload_post_wf false⟩,by simp [payloadPost,payloadCandidate,selfDependent,fixture,l0]⟩

/-- Deliberately wrong candidates stay private to this counterexample module. -/
private def forceOccurrence (s : State) (l : RootLocationId) (o : OccurrenceId) : State := by
  classical
  exact {s with
    root := fun m => if m = l then {s.root m with occurrence := some o} else s.root m
    usedOccurrences := insert o s.usedOccurrences }
private def wrongWhole : State :=
  forceOccurrence (wholeCandidate independent l0 (pkg 2) (alloc 0 1) true) l0 (occ 0)
private def wrongPayload : State := forceOccurrence (payloadPost true) l0 (occ 100)
private def wrongSame : State := forceOccurrence selfDependent l0 (occ 100)
private def wrongSwapPreserved : State :=
  forceOccurrence (forceOccurrence (swapCandidate independent l0 l1 (alloc 0 1) (alloc 1 1)) l0 (occ 0)) l1 (occ 1)
private def wrongSwapTransferred : State :=
  forceOccurrence (forceOccurrence (swapCandidate independent l0 l1 (alloc 0 1) (alloc 1 1)) l0 (occ 1)) l1 (occ 0)

theorem whole_replace_preserving_old_occurrence_is_broken :
    ¬ RawWhole True True independent l0 (pkg 2) (value 1 ∅) (alloc 0 1) true wrongWhole := by
  intro raw
  have eq := whole_new_occurrence_equation raw
  simp [wrongWhole,forceOccurrence,alloc,occ] at eq

theorem same_variant_whole_replace_reusing_old_occurrence_is_broken :
    ¬ RawWhole True True independent l0 (pkg 2) (value 1 ∅)
      ⟨vf 100,some (vf 110,occ 0)⟩ true
      (wholeCandidate independent l0 (pkg 2) ⟨vf 100,some (vf 110,occ 0)⟩ true) := by
  intro raw
  exact fresh_allocation_cannot_reuse_occurrence raw.fresh rfl (by simp [independent,fixture])

theorem payload_only_replacement_allocating_occurrence_is_broken :
    ¬ RawPayload True True selfDependent l0 (pkg 4) (pkg 5) (value 1 {.occurrence (occ 0)})
      ⟨44,∅⟩ true (vf 100) (vf 110) true wrongPayload := by
  intro raw
  have eq := (payload_preserves_occurrence raw).1
  simp [wrongPayload,forceOccurrence,selfDependent,fixture,l0,occ] at eq

theorem same_place_swap_allocating_occurrence_is_broken :
    ¬ RawSwap True True selfDependent l0 l0 wrongSame := by
  intro raw
  have eq := congrArg (fun s => (s.root l0).occurrence) (swap_same_is_identity raw)
  simp [wrongSame,forceOccurrence,selfDependent,fixture,l0,occ] at eq

theorem distinct_swap_preserving_source_occurrences_is_broken :
    ¬ RawSwapDistinct True True independent l0 l1 (value 1 ∅) (value 1 ∅)
      (alloc 0 1) (alloc 1 1) wrongSwapPreserved := by
  intro raw
  have eq := congrArg SumRoot.occurrence (swap_distinct_target_equations raw).1
  simp [wrongSwapPreserved,forceOccurrence,installRoot,alloc,l0,l1,occ] at eq

theorem distinct_swap_transferring_occurrence_with_value_is_broken :
    ¬ RawSwapDistinct True True independent l0 l1 (value 1 ∅) (value 1 ∅)
      (alloc 0 1) (alloc 1 1) wrongSwapTransferred := by
  intro raw
  have eq := congrArg SumRoot.occurrence (swap_distinct_target_equations raw).1
  simp [wrongSwapTransferred,forceOccurrence,installRoot,alloc,l0,l1,occ] at eq

theorem whole_value_result_preserves_payload_but_not_occurrence :
    (wholeCandidate independent l0 (pkg 2) (alloc 0 1) true).values (pkg 0) = some (.sum (value 1 ∅)) ∧
    Survives (wholeCandidate independent l0 (pkg 2) (alloc 0 1) true) (pkg 0) ∧
    Fact.occurrence (occ 0) ∉ LiveFacts (wholeCandidate independent l0 (pkg 2) (alloc 0 1) true) := by
  exact whole_replace_value_transfers_without_occurrence independent_wf independent_whole_replace_is_legal.2.1
    (by simp [independent,fixture,pkg,l0]) (by simp [independent,fixture,l0])

theorem whole_vs_payload_only_occurrence_contrast :
    ((wholeCandidate independent l0 (pkg 2) (alloc 0 1) true).root l0).occurrence = some (occ 100) ∧
    ((payloadPost true).root l0).occurrence = some (occ 0) ∧
    (payloadPost true).usedOccurrences = selfDependent.usedOccurrences :=
  ⟨same_variant_whole_replace_restarts_occurrence,payload_only_replace_preserves_occurrence_with_self_dependency.2,
    (payload_preserves_occurrence (payload_raw true)).2⟩

theorem omitting_static_sum_discardability_can_silently_lose_value :
    WellFormed nonDiscardableNone ∧
    WellFormed (wholeCandidate nonDiscardableNone l0 (pkg 2) (alloc 0 1) false) ∧
    ¬ RawWhole True True nonDiscardableNone l0 (pkg 2) (value 1 ∅) (alloc 0 1) false
      (wholeCandidate nonDiscardableNone l0 (pkg 2) (alloc 0 1) false) := by
  have pre : WellFormed nonDiscardableNone := by
    apply fixture_shape _ _ _ _ _ _ _ _ (by simp) (by simp)
    apply fixture_dependencies <;> simp
  refine ⟨pre,whole_post_wf _ _ _ _ _ _ _ _ _ pre (by apply whole_dependencies <;> simp),?_⟩
  intro raw
  have enabled := raw.discardable rfl
  simp [nonDiscardableNone,fixture,sumType,SumType.discardable] at enabled

theorem reused_pair_occurrence_allocation_is_rejected :
    ¬ FreshPair independent (alloc 0 1) ⟨vf 101,some (vf 111,occ 100)⟩ := by
  intro pair
  have disjoint := Finset.disjoint_left.mp pair.2.2.2
  exact disjoint (a := occ 100)
    (by simp [alloc,Allocation.occurrences]) (by simp [Allocation.occurrences])

theorem all_negative_dependency_fixtures_have_wellFormed_pre_states :
    WellFormed withIncomingDependency ∧ WellFormed withExternalDependency ∧
    WellFormed (fixture 1 1 true {.occurrence (occ 1)} ∅ ∅ ∅ ∅) ∧
    WellFormed (fixture 1 1 true ∅ {.occurrence (occ 1)} ∅ ∅ ∅) ∧
    WellFormed (fixture 1 1 true ∅ {.occurrence (occ 0)} ∅ ∅ ∅) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply occurrence_fixture_wf <;> simp [allowedOccurrences]

private def retargetFact : Fact → Fact
  | .occurrence o => if o = occ 0 then .occurrence (occ 100)
      else if o = occ 1 then .occurrence (occ 101) else .occurrence o
  | f => f
private def retargetValue : SemanticValue → SemanticValue
  | .sum v => .sum {v with
      rootDependencies := v.rootDependencies.image retargetFact
      payload := v.payload.map (fun p => {p with dependencies := p.dependencies.image retargetFact})}
  | .payload v cap => .payload {v with dependencies := v.dependencies.image retargetFact} cap
private def wrongRetargetSwap : State :=
  let post := swapCandidate cyclic l0 l1 (alloc 0 1) (alloc 1 1)
  {post with values := fun p => (post.values p).map retargetValue}

theorem rewriting_dependencies_to_fresh_occurrences_is_not_raw_swap :
    ¬ RawSwapDistinct True True cyclic l0 l1
      (value 1 {.occurrence (occ 1)}) (value 1 {.occurrence (occ 0)})
      (alloc 0 1) (alloc 1 1) wrongRetargetSwap := by
  intro raw
  have table := (swap_distinct_exchanges_values_without_rewriting_dependencies raw).1
  have unchanged := congrArg (fun values => values (pkg 0)) table
  have equality := congrArg (Option.map SemanticValue.dependencies) unchanged
  simp [wrongRetargetSwap,swapCandidate,cyclic,fixture,pkg,retargetValue,retargetFact,
    SemanticValue.dependencies,SumValue.dependencies,value,occ] at equality

end
end NewLang.F1.Conditional.Counterexample.Sum
