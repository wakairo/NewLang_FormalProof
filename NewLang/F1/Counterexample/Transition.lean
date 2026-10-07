import NewLang.F1.Swap
import NewLang.F1.FixedChange
import NewLang.F1.FixedLifetime

namespace NewLang.F1.Counterexample.Transition
open F0
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

private def p0 : PlaceId := ⟨0⟩
private def a : PlaceId := ⟨1⟩
private def b : PlaceId := ⟨2⟩
private def x : PlaceId := ⟨3⟩
private def y : PlaceId := ⟨4⟩
private def bx : PlaceId := ⟨5⟩
private def byp : PlaceId := ⟨6⟩
private def c : PlaceId := ⟨7⟩
private def loc : RootLocationId := ⟨0⟩
private def input : PackageId := ⟨100⟩
private def output : PackageId := ⟨200⟩
private def places : Finset PlaceId := {p0,a,b,x,y,bx,byp,c}
private def path (p : PlaceId) : List Nat :=
  if p = p0 then [] else if p = a then [0] else if p = b then [1]
  else if p = x then [0,0] else if p = y then [0,1]
  else if p = bx then [1,0] else if p = byp then [1,1] else [2]
private def layout : StructuralLayout := ⟨places,p0,path⟩
private def target (p : PlaceId) : StructuralTarget := ⟨loc,p⟩
private def atom (p : PlaceId) : Fact := .valueFact p ⟨p.index⟩
private def cap (allow : Bool) (_p : PlaceId) : Bool := allow
private def node (deps : PlaceId → Finset Fact) (p : PlaceId) : StructuralNodeState :=
  ⟨⟨p.index⟩,⟨p.index⟩,deps p⟩
private def seed (deps : PlaceId → Finset Fact) (allow : Bool) : CurrentState where
  base := {
    liveRoots := {loc}
    root := fun _ => ⟨layout,node deps,⟨0⟩,⟨0⟩,allow⟩
    loosePackages := ∅
    looseValues := fun _ => none
    liveDomains := {⟨0⟩}
    domainValueCarrier := fun d => if d = ⟨0⟩ then some ⟨0⟩ else none
    usedValueFacts := places.image (fun p => (⟨p.index⟩ : ValueFactId))
    usedIncarnations := places.image (fun p => (⟨p.index⟩ : IncarnationId)) }
  content := fun _ p => p.index
  capability := fun _ p => cap allow p
  carried := fun _ => none

private theorem place_cases {p : PlaceId} (tracked : p ∈ places) :
    p = p0 ∨ p = a ∨ p = b ∨ p = x ∨ p = y ∨ p = bx ∨ p = byp ∨ p = c := by
  simpa [places] using tracked

private theorem tree : TreeWellFormed layout := by
  constructor
  · simp [layout,places]
  · simp [layout,path]
  · intro p pt q qt same
    rcases place_cases pt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [layout,path,p0,a,b,x,y,bx,byp,c]
  · intro p pt nonroot
    rcases place_cases pt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact False.elim (nonroot rfl)
    · exact ⟨p0, by simp [layout,places],0,by simp [layout,path,p0,a]⟩
    · exact ⟨p0, by simp [layout,places],1,by simp [layout,path,p0,a,b]⟩
    · exact ⟨a, by simp [layout,places],0,by simp [layout,path,p0,a,b,x]⟩
    · exact ⟨a, by simp [layout,places],1,by simp [layout,path,p0,a,b,x,y]⟩
    · exact ⟨b, by simp [layout,places],0,by simp [layout,path,p0,a,b,x,y,bx]⟩
    · exact ⟨b, by simp [layout,places],1,by simp [layout,path,p0,a,b,x,y,bx,byp]⟩
    · exact ⟨p0, by simp [layout,places],2,by simp [layout,path,p0,a,b,x,y,bx,byp,c]⟩

private theorem seed_wf (deps : PlaceId → Finset Fact) (allow : Bool)
    (valid : ∀ p ∈ places, ∀ f ∈ deps p, f ∈ StructuralLiveFacts (seed deps allow).base) :
    CurrentWellFormed (seed deps allow) := by
  refine ⟨?_, by simp [seed], ?_⟩
  · constructor
    · intro l _; exact tree
    · intro l m p lh mh; exact (Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm
    · intro l p m q lh mh same
      refine ⟨(Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm, ?_⟩
      cases p; cases q; simpa [seed,node] using same
    · intro l p m q lh mh same
      refine ⟨(Finset.mem_singleton.mp lh.1).trans (Finset.mem_singleton.mp mh.1).symm, ?_⟩
      cases p; cases q; simpa [seed,node] using same
    · intro l lt m mt _; exact (Finset.mem_singleton.mp lt).trans (Finset.mem_singleton.mp mt).symm
    · simp [seed]
    · simp [seed]
    · simp [seed]
    · intro l p live f dep; exact valid p live.2 f dep
    · simp [seed]
    · intro l p live; exact Finset.mem_image.mpr ⟨p,live.2,rfl⟩
    · intro l p live; exact Finset.mem_image.mpr ⟨p,live.2,rfl⟩
    · intro d; by_cases eq : d = ⟨0⟩ <;> simp [seed,eq]
  · intro l _; simp [seed,cap,layout]

private def emptyDeps : PlaceId → Finset Fact := fun _ => ∅
private def incomingValue (s : CurrentState) (p : PlaceId) (deps : List Nat → Finset Fact) : StructuredValue :=
  { extractValue s (target p) with fragment := fun k => ⟨100 + k.length, deps k⟩ }
private def before (p : PlaceId) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) : CurrentState :=
  let s := seed oldDeps allow
  let v := incomingValue s p newDeps
  { s with
    base := { s.base with
      loosePackages := {input}
      looseValues := fun pkg => if pkg = input then some v.summary else none }
    carried := fun pkg => if pkg = input then some v else none }
private def newValue (p : PlaceId) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) : StructuredValue :=
  incomingValue (seed oldDeps allow) p newDeps
private def supply (q : NodeKey) : ValueFactId := ⟨100 + q.2.index⟩

private theorem before_wf (p : PlaceId) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool)
    (oldValid : ∀ q ∈ places, ∀ f ∈ oldDeps q, f ∈ StructuralLiveFacts (seed oldDeps allow).base)
    (newValid : ∀ k ∈ (newValue p oldDeps newDeps allow).shape, ∀ f ∈ newDeps k,
      f ∈ StructuralLiveFacts (seed oldDeps allow).base) :
    CurrentWellFormed (before p oldDeps newDeps allow) := by
  classical
  have wf := seed_wf oldDeps allow oldValid
  refine ⟨{ wf.structural with installedNotLoose := ?_, loosePresent := ?_, looseDependenciesValid := ?_ }, ?_, wf.rootCapability⟩
  · intro l _; simp [before,seed,input]
  · intro pkg loose
    have eq : pkg = input := Finset.mem_singleton.mp loose
    subst pkg; exact ⟨(newValue p oldDeps newDeps allow).summary, by simp [before,newValue]⟩
  · intro pkg loose value eq f dep
    have same : pkg = input := Finset.mem_singleton.mp loose
    subst pkg
    have valueEq : value = (newValue p oldDeps newDeps allow).summary := by
      apply Option.some.inj; simpa [before,newValue] using eq.symm
    subst value
    rcases Finset.mem_biUnion.mp dep with ⟨k,kt,owned⟩
    exact newValid k kt f owned
  · intro pkg loose
    have same : pkg = input := Finset.mem_singleton.mp loose
    subst pkg; exact ⟨newValue p oldDeps newDeps allow, by simp [before,newValue], by simp [before,newValue]⟩

private theorem baseline_empty (p : PlaceId) (allow : Bool) :
    CurrentWellFormed (before p emptyDeps (fun _ => ∅) allow) :=
  before_wf _ _ _ _ (by simp [emptyDeps]) (by simp)

-- Normalize this finite model without introducing any custom semantic assumptions.
private theorem below_iff_prefix {p q : PlaceId} (pt : p ∈ places) (qt : q ∈ places) :
    Below layout p q ↔ path p <+: path q := by
  constructor
  · intro below; exact ⟨relativePosition ((seed emptyDeps true).base.root loc) p q,
      (below_path_decomposition (r := (seed emptyDeps true).base.root loc) below).symm⟩
  · rintro ⟨suffix, eq⟩
    by_cases empty : suffix = []
    · subst suffix; exact Or.inl (tree.paths_unique p pt q qt (by simpa only [layout,List.append_nil] using eq))
    · exact Or.inr ⟨pt,qt,suffix,empty,eq.symm⟩

private theorem subtree_mem (deps : PlaceId → Finset Fact) (allow : Bool) (p q : PlaceId) (pt : p ∈ places) :
    q ∈ subtreePlaces ((seed deps allow).base.root loc) p ↔ q ∈ places ∧ path p <+: path q := by
  classical
  change q ∈ places.filter (Below layout p) ↔ q ∈ places ∧ path p <+: path q
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨qt,below⟩; exact ⟨qt,(below_iff_prefix pt qt).mp below⟩
  · rintro ⟨qt,isPrefix⟩; exact ⟨qt,(below_iff_prefix pt qt).mpr isPrefix⟩

private theorem fresh_supply (p : PlaceId) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) :
    FreshStructuralFacts (before p oldDeps newDeps allow).base
      (affectedBy (before p oldDeps newDeps allow).base (target p)) supply := by
  classical
  constructor
  · intro q changed old
    have live := (mem_affectedBy.mp changed).1
    have tracked := place_cases live.2
    rcases Finset.mem_image.mp old with ⟨r,rt,same⟩
    have rt := place_cases rt
    rcases tracked with eq|eq|eq|eq|eq|eq|eq|eq <;>
      rcases rt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [supply,p0,a,b,x,y,bx,byp,c]
  · intro q qc r rc same
    have qloc := (mem_affectedBy.mp qc).2.1
    have rloc := (mem_affectedBy.mp rc).2.1
    have indices : q.2.index = r.2.index := by
      have := congrArg ValueFactId.index same
      simp only [supply] at this; omega
    have placeEq : q.2 = r.2 := congrArg PlaceId.mk indices
    exact Prod.ext (qloc.trans rloc.symm) placeEq


private structure FixedFrame (s post : CurrentState) : Prop where
  liveRoots : post.base.liveRoots = s.base.liveRoots
  layout : ∀ l, (post.base.root l).layout = (s.base.root l).layout
  incarnation : ∀ l p, ((post.base.root l).node p).incarnation = ((s.base.root l).node p).incarnation
  governing : ∀ l, (post.base.root l).governing = (s.base.root l).governing
  discardable : ∀ l, (post.base.root l).discardable = (s.base.root l).discardable
  domains : post.base.liveDomains = s.base.liveDomains
  domainCarrier : post.base.domainValueCarrier = s.base.domainValueCarrier
  incHistory : post.base.usedIncarnations = s.base.usedIncarnations
  capability : post.capability = s.capability

/-- Private fixture verification: structural invariants are inherited; survivor
checks are supplied separately and cannot be replaced by a pre-state dependency check. -/
private theorem checked_post (s post : CurrentState) (wf : CurrentWellFormed s)
    (single : s.base.liveRoots = {loc}) (frame : FixedFrame s post)
    (support : Finset NodeKey) (fresh : NodeKey → ValueFactId)
    (allocation : FreshStructuralFacts s.base support fresh)
    (facts : ∀ l p, ((post.base.root l).node p).currentFact =
      (((refreshCurrentFacts s.base support fresh).root l).node p).currentFact)
    (history : post.base.usedValueFacts = (refreshCurrentFacts s.base support fresh).usedValueFacts)
    (carrier : ∀ l ∈ post.base.liveRoots, (post.base.root l).package ∉ post.base.loosePackages)
    (localValid : ∀ l p, LiveNode post.base l p → ∀ f ∈ LocalDeps (post.base.root l) p,
      f ∈ StructuralLiveFacts post.base)
    (looseValid : ∀ pkg ∈ post.base.loosePackages, ∃ v,
      post.carried pkg = some v ∧ post.base.looseValues pkg = some v.summary ∧
      ∀ f ∈ v.dependencies, f ∈ StructuralLiveFacts post.base) : CurrentWellFormed post := by
  have liveEq : ∀ l p, LiveNode post.base l p ↔ LiveNode s.base l p := by
    intro l p; simp only [LiveNode,frame.liveRoots,frame.layout]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro l lt; rw [frame.layout]; exact wf.structural.trees l (frame.liveRoots ▸ lt)
    · intro l m p lp mp; exact wf.structural.placesUnique l m p ((liveEq l p).mp lp) ((liveEq m p).mp mp)
    · intro l p m q lp mq eq
      rw [frame.incarnation,frame.incarnation] at eq
      exact wf.structural.incarnationsUnique l p m q ((liveEq l p).mp lp) ((liveEq m q).mp mq) eq
    · intro l p m q lp mq eq
      rw [facts,facts] at eq
      exact refreshed_current_facts_unique wf.structural allocation ((liveEq l p).mp lp) ((liveEq m q).mp mq) eq
    · intro l lt m mt _
      rw [frame.liveRoots,single] at lt mt
      exact (Finset.mem_singleton.mp lt).trans (Finset.mem_singleton.mp mt).symm
    · exact carrier
    · intro pkg loose; rcases looseValid pkg loose with ⟨v,_,data,_⟩; exact ⟨v.summary,data⟩
    · intro l lt; rw [frame.governing,frame.domains]; exact wf.structural.domainsValid l (frame.liveRoots ▸ lt)
    · exact localValid
    · intro pkg loose v eq f dep
      rcases looseValid pkg loose with ⟨value,_,data,valid⟩
      have same : v = value.summary := Option.some.inj (eq.symm.trans data)
      subst v; exact valid f dep
    · intro l p live; rw [facts,history]
      exact refreshed_current_facts_recorded wf.structural support fresh ((liveEq l p).mp live)
    · intro l p live; rw [frame.incarnation,frame.incHistory]
      exact wf.structural.incarnationsRecorded l p ((liveEq l p).mp live)
    · intro d; rw [frame.domains,frame.domainCarrier]; exact wf.structural.domainCarrierCoherent d
  · intro pkg loose; rcases looseValid pkg loose with ⟨v,value,data,_⟩; exact ⟨v,value,data⟩
  · intro l lt; rw [frame.capability,frame.layout,frame.discardable]
    exact wf.rootCapability l (frame.liveRoots ▸ lt)

private theorem empty_extract (s : CurrentState) (wf : CurrentWellFormed s) (p : PlaceId)
    (live : loc ∈ s.base.liveRoots) (empty : ∀ q, LocalDeps (s.base.root loc) q = ∅) :
    (extractValue s (target p)).dependencies = ∅ := by
  rw [extract_value_dependencies wf live]
  unfold SubtreeDeps
  have functions : LocalDeps (s.base.root loc) = (fun _ => ∅) := funext empty
  change (subtreePlaces (s.base.root loc) p).biUnion (LocalDeps (s.base.root loc)) = ∅
  rw [functions]; ext f; simp

private theorem new_fits (p : PlaceId) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) (wf : CurrentWellFormed (before p oldDeps newDeps allow)) :
    FitsTarget (before p oldDeps newDeps allow) (target p) (newValue p oldDeps newDeps allow) := by
  refine ⟨rfl, ?_⟩
  intro q inside
  exact (extract_value_fragment wf (by simp [before,seed,target]) inside).2

private theorem raw_replace (p : PlaceId) (pt : p ∈ places) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) (wf : CurrentWellFormed (before p oldDeps newDeps allow)) :
    RawStructuralReplace True True (before p oldDeps newDeps allow) (target p) input
      (if p = p0 then ⟨0⟩ else output) (newValue p oldDeps newDeps allow) supply
      (structuralReplaceCandidate (before p oldDeps newDeps allow) (target p) input
        (if p = p0 then ⟨0⟩ else output) (newValue p oldDeps newDeps allow) supply) := by
  classical
  constructor
  · exact ⟨by simp [before,seed,target],pt⟩
  · simp [before]
  · simp [before,newValue]
  · exact new_fits _ _ _ _ wf
  · by_cases root : p = p0
    · simp [target,before,seed,layout,root]
    · simp [target,before,seed,layout,root,output,input]
  · exact fresh_supply _ _ _ _
  · trivial
  · trivial
  · rfl

private theorem raw_store (p : PlaceId) (pt : p ∈ places)
    (oldDeps : PlaceId → Finset Fact) (newDeps : List Nat → Finset Fact)
    (wf : CurrentWellFormed (before p oldDeps newDeps true)) :
    RawStructuralStore True True (before p oldDeps newDeps true) (target p) input
      (newValue p oldDeps newDeps true) supply
      (structuralStoreCandidate (before p oldDeps newDeps true) (target p) input (newValue p oldDeps newDeps true) supply) := by
  constructor
  · exact ⟨by simp [before,seed,target],pt⟩
  · simp [before]
  · simp [before,newValue]
  · exact new_fits _ _ _ _ wf
  · simp [before,seed,target,cap]
  · exact fresh_supply _ _ _ _
  · trivial
  · trivial
  · rfl

private theorem independent_replace (p : PlaceId) (pt : p ∈ places) :
    StructuralReplaceStep True True (before p emptyDeps (fun _ => ∅) true) (target p) input
      (if p = p0 then ⟨0⟩ else output) (newValue p emptyDeps (fun _ => ∅) true) supply
      (structuralReplaceCandidate (before p emptyDeps (fun _ => ∅) true) (target p) input
        (if p = p0 then ⟨0⟩ else output) (newValue p emptyDeps (fun _ => ∅) true) supply) := by
  classical
  let s := before p emptyDeps (fun _ => ∅) true
  let result : PackageId := if p = p0 then ⟨0⟩ else output
  let v := newValue p emptyDeps (fun _ => ∅) true
  let post := structuralReplaceCandidate s (target p) input result v supply
  have wf : CurrentWellFormed s := baseline_empty p true
  have raw := raw_replace p pt emptyDeps (fun _ => ∅) true wf
  refine ⟨wf,raw,?_⟩
  apply checked_post s post wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (affectedBy s.base (target p)) supply raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l live
    have same : l = loc := Finset.mem_singleton.mp live
    subst l
    by_cases root : p = p0
    · simp [post,structuralReplaceCandidate,installValue,s,before,seed,target,layout,result,root,input]
    · simp [post,structuralReplaceCandidate,installValue,s,before,seed,target,layout,result,root,input,output]
  · intro l q _ f dep
    simp [post,structuralReplaceCandidate,installValue,LocalDeps,s,before,seed,node,emptyDeps,v,newValue,incomingValue] at dep
  · intro pkg loose
    have same : pkg = result := by simpa [post,structuralReplaceCandidate,installValue,s,before] using loose
    subst pkg
    refine ⟨extractValue s (target p),?_,?_,?_⟩
    · simp [post,structuralReplaceCandidate]
    · simp [post,structuralReplaceCandidate]
    · have empty := empty_extract s wf p (by simp [s,before,seed]) (by intro q; rfl)
      simp [empty]


private theorem overlap_iff_prefixes {p q : PlaceId} (pt : p ∈ places) (qt : q ∈ places) :
    StructuralOverlap layout p q ↔ path p <+: path q ∨ path q <+: path p := by
  constructor
  · rintro (rfl | pq | qp)
    · exact Or.inl List.prefix_rfl
    · exact Or.inl ((below_iff_prefix pt qt).mp (Or.inr pq))
    · exact Or.inr ((below_iff_prefix qt pt).mp (Or.inr qp))
  · rintro (pq | qp)
    · rcases (below_iff_prefix pt qt).mpr pq with eq | anc
      · exact Or.inl eq
      · exact Or.inr (Or.inl anc)
    · rcases (below_iff_prefix qt pt).mpr qp with eq | anc
      · exact Or.inl eq.symm
      · exact Or.inr (Or.inr anc)

private theorem affected_mem (p : PlaceId) (pt : p ∈ places) (oldDeps : PlaceId → Finset Fact)
    (newDeps : List Nat → Finset Fact) (allow : Bool) (l : RootLocationId) (q : PlaceId) :
    (l,q) ∈ affectedBy (before p oldDeps newDeps allow).base (target p) ↔
    l = loc ∧ q ∈ places ∧ (path p <+: path q ∨ path q <+: path p) := by
  classical
  rw [mem_affectedBy]
  change ((l ∈ ({loc} : Finset RootLocationId) ∧ q ∈ places) ∧ l = loc ∧ StructuralOverlap layout p q) ↔ _
  simp only [Finset.mem_singleton]
  by_cases qt : q ∈ places
  · rw [overlap_iff_prefixes pt qt]; simp [qt]
  · simp [qt]

private theorem affected_x :
    affectedBy (before x emptyDeps (fun _ => ∅) true).base (target x) = {(loc,p0),(loc,a),(loc,x)} := by
  classical
  ext key; rcases key with ⟨l,q⟩
  rw [affected_mem x (by simp [places])]
  by_cases qt : q ∈ places
  · rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [path,p0,a,b,x,y,bx,byp,c,loc,places]
  · constructor
    · intro h; exact False.elim (qt h.2.1)
    · intro h; simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
      rcases h with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩ <;> simp [places] at qt

private theorem affected_a :
    affectedBy (before a emptyDeps (fun _ => ∅) true).base (target a) = {(loc,p0),(loc,a),(loc,x),(loc,y)} := by
  classical
  ext key; rcases key with ⟨l,q⟩
  rw [affected_mem a (by simp [places])]
  by_cases qt : q ∈ places
  · rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [path,p0,a,b,x,y,bx,byp,c,loc,places]
  · constructor
    · intro h; exact False.elim (qt h.2.1)
    · intro h; simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
      rcases h with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩ <;> simp [places] at qt

private def independentPost (p : PlaceId) : CurrentState :=
  structuralReplaceCandidate (before p emptyDeps (fun _ => ∅) true) (target p) input
    (if p = p0 then ⟨0⟩ else output) (newValue p emptyDeps (fun _ => ∅) true) supply

theorem leaf_replace_is_legal :
    StructuralReplaceStep True True (before x emptyDeps (fun _ => ∅) true) (target x) input output
      (newValue x emptyDeps (fun _ => ∅) true) supply (independentPost x) := by
  simpa [independentPost,x,p0] using independent_replace x (by simp [places])

theorem nested_aggregate_replace_is_legal :
    StructuralReplaceStep True True (before a emptyDeps (fun _ => ∅) true) (target a) input output
      (newValue a emptyDeps (fun _ => ∅) true) supply (independentPost a) := by
  simpa [independentPost,a,p0] using independent_replace a (by simp [places])

theorem whole_root_replace_is_legal :
    StructuralReplaceStep True True (before p0 emptyDeps (fun _ => ∅) true) (target p0) input ⟨0⟩
      (newValue p0 emptyDeps (fun _ => ∅) true) supply (independentPost p0) := by
  simpa [independentPost] using independent_replace p0 (by simp [places])

theorem leaf_replace_freshens_root_left_leaf_and_frames_siblings :
    (∀ p ∈ ({p0,a,x} : Finset PlaceId),
      (((independentPost x).base.root loc).node p).currentFact = supply (loc,p)) ∧
    (∀ p ∈ ({y,b,bx,byp,c} : Finset PlaceId),
      (((independentPost x).base.root loc).node p).currentFact = ⟨p.index⟩ ∧
      LocalDeps ((independentPost x).base.root loc) p = ∅ ∧
      (((independentPost x).base.root loc).node p).incarnation = ⟨p.index⟩) := by
  classical
  constructor
  · intro p pt
    rw [replace_current_fact_equation leaf_replace_is_legal.2.1,affected_x]
    simp only [Finset.mem_insert,Finset.mem_singleton] at pt
    rcases pt with rfl|rfl|rfl <;> simp
  · intro p pt
    refine ⟨?_, ?_, replace_preserves_all_incarnations leaf_replace_is_legal.2.1 loc p⟩
    · rw [replace_current_fact_equation leaf_replace_is_legal.2.1,affected_x]
      simp only [Finset.mem_insert,Finset.mem_singleton] at pt
      rcases pt with rfl|rfl|rfl|rfl|rfl <;> simp [before,seed,node,p0,a,b,x,y,bx,byp,c]
    · change (if _ then ∅ else ∅) = ∅
      split <;> rfl

theorem nested_replace_freshens_descendants_and_preserves_right :
    (∀ p ∈ ({p0,a,x,y} : Finset PlaceId),
      (((independentPost a).base.root loc).node p).currentFact = supply (loc,p)) ∧
    (((independentPost a).base.root loc).node b).currentFact = ⟨2⟩ := by
  classical
  constructor
  · intro p pt
    rw [replace_current_fact_equation nested_aggregate_replace_is_legal.2.1,affected_a]
    simp only [Finset.mem_insert,Finset.mem_singleton] at pt
    rcases pt with rfl|rfl|rfl|rfl <;> simp
  · rw [replace_current_fact_equation nested_aggregate_replace_is_legal.2.1,affected_a]
    simp [before,seed,node,p0,a,b,x,y]

theorem whole_root_replace_freshens_all_fixed_nodes :
    ∀ p ∈ places, (((independentPost p0).base.root loc).node p).currentFact = supply (loc,p) ∧
      (((independentPost p0).base.root loc).node p).incarnation = ⟨p.index⟩ := by
  intro p pt
  have below := root_contains_every_place tree pt
  have overlap : StructuralOverlap layout p0 p := by
    rcases below with eq|anc
    · exact Or.inl eq
    · exact Or.inr (Or.inl anc)
  have changed := (mem_affectedBy (s := (before p0 emptyDeps (fun _ => ∅) true).base)
    (t := target p0)).mpr ⟨⟨by simp [before,seed,target],pt⟩,rfl,overlap⟩
  exact ⟨(replace_freshens_affected whole_root_replace_is_legal.2.1 changed).1,
    replace_preserves_all_incarnations whole_root_replace_is_legal.2.1 loc p⟩


private def oneDependency (owner source : PlaceId) : PlaceId → Finset Fact :=
  fun q => if q = owner then {atom source} else ∅

private theorem atom_live (deps : PlaceId → Finset Fact) (allow : Bool) {p : PlaceId} (pt : p ∈ places) :
    atom p ∈ StructuralLiveFacts (seed deps allow).base := ⟨loc,by simp [seed],pt,rfl⟩

private theorem one_dependency_wf (p owner source : PlaceId) (st : source ∈ places) (allow : Bool) :
    CurrentWellFormed (before p (oneDependency owner source) (fun _ => ∅) allow) := by
  apply before_wf
  · intro q _ f dep
    by_cases same : q = owner
    · have eq : f = atom source := by simpa [oneDependency,same] using dep
      subst f; exact atom_live _ _ st
    · simp [oneDependency,same] at dep
  · simp

private theorem target_inside (p : PlaceId) (pt : p ∈ places) (deps : PlaceId → Finset Fact) (allow : Bool) :
    p ∈ subtreePlaces ((seed deps allow).base.root loc) p := by
  classical
  exact Finset.mem_filter.mpr ⟨pt,Or.inl rfl⟩

private theorem store_old_self_legal (p : PlaceId) (pt : p ∈ places) :
    StructuralStoreStep True True (before p (oneDependency p p) (fun _ => ∅) true) (target p) input
      (newValue p (oneDependency p p) (fun _ => ∅) true) supply
      (structuralStoreCandidate (before p (oneDependency p p) (fun _ => ∅) true) (target p) input
        (newValue p (oneDependency p p) (fun _ => ∅) true) supply) := by
  classical
  let s := before p (oneDependency p p) (fun _ => ∅) true
  let v := newValue p (oneDependency p p) (fun _ => ∅) true
  let post := structuralStoreCandidate s (target p) input v supply
  have wf : CurrentWellFormed s := one_dependency_wf p p p pt true
  have raw := raw_store p pt (oneDependency p p) (fun _ => ∅) wf
  refine ⟨wf,raw,?_⟩
  apply checked_post s post wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (affectedBy s.base (target p)) supply raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l _; simp [post,structuralStoreCandidate,installValue,s,before]
  · intro l q live f dep
    have sameLoc : l = loc := Finset.mem_singleton.mp live.1
    subst l
    change f ∈ (if loc = (target p).location ∧ q ∈ subtreePlaces (s.base.root loc) p then ∅
      else if q = p then {atom p} else ∅) at dep
    by_cases same : q = p
    · subst q
      have inside := target_inside p pt (oneDependency p p) true
      simp [target,inside,s,before] at dep
    · simp [same] at dep
  · intro pkg loose; simp [post,structuralStoreCandidate,installValue,s,before] at loose

theorem store_eliminates_old_only_structural_dependency :
    StructuralStoreStep True True (before x (oneDependency x x) (fun _ => ∅) true) (target x) input
      (newValue x (oneDependency x x) (fun _ => ∅) true) supply
      (structuralStoreCandidate (before x (oneDependency x x) (fun _ => ∅) true) (target x) input
        (newValue x (oneDependency x x) (fun _ => ∅) true) supply) :=
  store_old_self_legal x (by simp [places])

theorem nested_store_eliminates_old_only_dependency :
    StructuralStoreStep True True (before a (oneDependency a a) (fun _ => ∅) true) (target a) input
      (newValue a (oneDependency a a) (fun _ => ∅) true) supply
      (structuralStoreCandidate (before a (oneDependency a a) (fun _ => ∅) true) (target a) input
        (newValue a (oneDependency a a) (fun _ => ∅) true) supply) :=
  store_old_self_legal a (by simp [places])

theorem replace_rejects_old_self_structural_dependency (post : CurrentState) :
    ¬ StructuralReplaceStep True True (before x (oneDependency x x) (fun _ => ∅) true) (target x) input output
      (newValue x (oneDependency x x) (fun _ => ∅) true) supply post := by
  have wf := one_dependency_wf x x x (by simp [places]) true
  apply replace_rejects_old_result_invalidated_dependency wf
    (l := loc) (p := x) (by exact ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩)
    (target_is_affected (by exact ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩))
  rw [extract_value_dependencies wf (by simp [before,seed,target])]
  exact local_deps_subset_subtree_deps (by simp [before,seed,layout,places,target])
    (by simp [LocalDeps,before,seed,node,oneDependency,atom,target])

theorem old_self_dependency_rejects_structural_replace_but_allows_store :
    (¬ StructuralReplaceStep True True (before x (oneDependency x x) (fun _ => ∅) true) (target x) input output
      (newValue x (oneDependency x x) (fun _ => ∅) true) supply
      (structuralReplaceCandidate (before x (oneDependency x x) (fun _ => ∅) true) (target x) input output
        (newValue x (oneDependency x x) (fun _ => ∅) true) supply)) ∧
    StructuralStoreStep True True (before x (oneDependency x x) (fun _ => ∅) true) (target x) input
      (newValue x (oneDependency x x) (fun _ => ∅) true) supply
      (structuralStoreCandidate (before x (oneDependency x x) (fun _ => ∅) true) (target x) input
        (newValue x (oneDependency x x) (fun _ => ∅) true) supply) :=
  ⟨replace_rejects_old_self_structural_dependency _,store_eliminates_old_only_structural_dependency⟩

private theorem incoming_dependency_wf :
    CurrentWellFormed (before x emptyDeps (fun _ => {atom x}) true) := by
  apply before_wf
  · simp [emptyDeps]
  · intro k _ f dep
    have same : f = atom x := Finset.mem_singleton.mp dep
    subst f; exact atom_live _ _ (by simp [places])

theorem incoming_old_structural_fact_rejects_replace_and_store (post : CurrentState) :
    (¬ StructuralReplaceStep True True (before x emptyDeps (fun _ => {atom x}) true) (target x) input output
      (newValue x emptyDeps (fun _ => {atom x}) true) supply post) ∧
    (¬ StructuralStoreStep True True (before x emptyDeps (fun _ => {atom x}) true) (target x) input
      (newValue x emptyDeps (fun _ => {atom x}) true) supply post) := by
  have live : LiveNode (before x emptyDeps (fun _ => {atom x}) true).base loc x :=
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩
  have inside := target_inside x (by simp [places]) emptyDeps true
  have affected := target_is_affected (t := target x) live
  exact ⟨replace_rejects_incoming_invalidated_dependency incoming_dependency_wf live affected inside (by simp [newValue,incomingValue,atom,before,seed,node]),
    store_rejects_incoming_invalidated_dependency incoming_dependency_wf live affected inside (by simp [newValue,incomingValue,atom,before,seed,node])⟩

theorem external_survivor_dependency_rejects_store (post : CurrentState) :
    ¬ StructuralStoreStep True True (before x (oneDependency b x) (fun _ => ∅) true) (target x) input
      (newValue x (oneDependency b x) (fun _ => ∅) true) supply post := by
  have wf := one_dependency_wf x b x (by simp [places]) true
  apply store_rejects_other_surviving_invalidated_dependency wf
    (l := loc) (p := x) (m := loc) (q := b)
    (by exact ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩)
    (target_is_affected (by exact ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩))
    (by exact ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩)
  · have outside : b ∉ subtreePlaces ((seed (oneDependency b x) true).base.root loc) x := by
      rw [subtree_mem _ _ _ _ (by simp [places])]
      simp [path,p0,a,b,x]
    simpa [target,before] using outside
  · simp [LocalDeps,before,seed,node,oneDependency,atom]

theorem nondiscardable_fixed_child_rejects_store (post : CurrentState) :
    ¬ RawStructuralStore True True (before x emptyDeps (fun _ => ∅) false) (target x) input
      (newValue x emptyDeps (fun _ => ∅) false) supply post :=
  store_rejects_nondiscardable_target (by simp [before,seed,target,cap])


private theorem subtree_leaf (deps : PlaceId → Finset Fact) (allow : Bool) (leaf : PlaceId)
    (isLeaf : leaf = x ∨ leaf = y) : subtreePlaces ((seed deps allow).base.root loc) leaf = {leaf} := by
  classical
  have lt : leaf ∈ places := by rcases isLeaf with rfl|rfl <;> simp [places]
  ext q
  rw [subtree_mem _ _ _ _ lt,Finset.mem_singleton]
  by_cases qt : q ∈ places
  · rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases isLeaf with rfl|rfl <;> simp [path,p0,a,b,x,y,bx,byp,c,places]
  · constructor
    · intro h; exact False.elim (qt h.1)
    · intro same; subst q; exact False.elim (qt lt)

private theorem leaf_shape (deps : PlaceId → Finset Fact) (allow : Bool) (leaf : PlaceId)
    (isLeaf : leaf = x ∨ leaf = y) : (extractValue (seed deps allow) (target leaf)).shape = {[]} := by
  classical
  change (subtreePlaces ((seed deps allow).base.root loc) leaf).image (relativePosition _ leaf) = {[]}
  rw [subtree_leaf deps allow leaf isLeaf]
  simp [relativePosition]

private theorem leaf_value_at_empty (deps : PlaceId → Finset Fact) (allow : Bool) (leaf : PlaceId)
    (lt : leaf ∈ places) (wf : CurrentWellFormed (seed deps allow)) :
    (extractValue (seed deps allow) (target leaf)).fragment [] = ⟨leaf.index,deps leaf⟩ ∧
    (extractValue (seed deps allow) (target leaf)).discardable [] = cap allow leaf := by
  simpa [relativePosition,seed,LocalDeps,node,target] using
    extract_value_fragment wf (t := target leaf) (by simp [seed,target]) (target_inside leaf lt deps allow)

private theorem swap_leaf_raw (deps : PlaceId → Finset Fact) (allow : Bool)
    (wf : CurrentWellFormed (seed deps allow)) :
    RawStructuralSwapDistinct True True (seed deps allow) (target x) (target y) supply
      (structuralSwapCandidate (seed deps allow) (target x) (target y) supply) := by
  classical
  constructor
  · exact ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩
  · exact ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩
  · right; refine ⟨rfl,?_⟩
    change KnownDisjoint layout x y
    rw [KnownDisjoint,overlap_iff_prefixes (by simp [places]) (by simp [places])]
    simp [path,p0,a,b,x,y]
  · refine ⟨by rw [leaf_shape _ _ x (Or.inl rfl),leaf_shape _ _ y (Or.inr rfl)],?_⟩
    intro q inside
    have same : q = x := by change q ∈ subtreePlaces ((seed deps allow).base.root loc) x at inside; rw [subtree_leaf _ _ x (Or.inl rfl)] at inside; exact Finset.mem_singleton.mp inside
    subst q
    simpa [relativePosition,seed,target,cap,p0,x,y] using (leaf_value_at_empty deps allow y (by simp [places]) wf).2
  · refine ⟨by rw [leaf_shape _ _ y (Or.inr rfl),leaf_shape _ _ x (Or.inl rfl)],?_⟩
    intro q inside
    have same : q = y := by change q ∈ subtreePlaces ((seed deps allow).base.root loc) y at inside; rw [subtree_leaf _ _ y (Or.inr rfl)] at inside; exact Finset.mem_singleton.mp inside
    subst q
    simpa [relativePosition,seed,target,cap,p0,x,y] using (leaf_value_at_empty deps allow x (by simp [places]) wf).2
  · constructor
    · intro q changed old
      have live : LiveNode (seed deps allow).base q.1 q.2 := by
        rcases Finset.mem_union.mp changed with left|right
        · exact (mem_affectedBy.mp left).1
        · exact (mem_affectedBy.mp right).1
      rcases Finset.mem_image.mp old with ⟨r,rt,same⟩
      rcases place_cases live.2 with eq|eq|eq|eq|eq|eq|eq|eq <;>
        rcases place_cases rt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp_all [supply,p0,a,b,x,y,bx,byp,c]
    · intro q qc r rc same
      have liveLoc : ∀ key ∈ swapAffected (seed deps allow).base (target x) (target y), key.1 = loc := by
        intro key member
        rcases Finset.mem_union.mp member with left|right
        · exact (mem_affectedBy.mp left).2.1
        · exact (mem_affectedBy.mp right).2.1
      have indices : q.2.index = r.2.index := by
        have := congrArg ValueFactId.index same; simp only [supply] at this; omega
      exact Prod.ext ((liveLoc q qc).trans (liveLoc r rc).symm) (congrArg PlaceId.mk indices)
  · trivial
  · trivial
  · rfl

private theorem seed_empty_wf (allow : Bool) : CurrentWellFormed (seed emptyDeps allow) :=
  seed_wf _ _ (by simp [emptyDeps])

private theorem independent_leaf_swap (allow : Bool) :
    StructuralSwapStep True True (seed emptyDeps allow) (target x) (target y)
      (structuralSwapCandidate (seed emptyDeps allow) (target x) (target y) supply) := by
  classical
  let s := seed emptyDeps allow
  let post := structuralSwapCandidate s (target x) (target y) supply
  have wf : CurrentWellFormed s := seed_empty_wf allow
  have raw := swap_leaf_raw emptyDeps allow wf
  refine ⟨wf,RawStructuralSwap.distinct raw,?_⟩
  apply checked_post s post wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (swapAffected s.base (target x) (target y)) supply raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l _; change _ ∉ (∅ : Finset PackageId); simp
  · intro l q live f dep
    have sameLoc : l = loc := Finset.mem_singleton.mp live.1
    subst l
    by_cases left : q ∈ subtreePlaces (s.base.root loc) x
    · have eq : q = x := by rw [subtree_leaf _ _ x (Or.inl rfl)] at left; exact Finset.mem_singleton.mp left
      subst q
      change f ∈ LocalDeps (post.base.root (target x).location) x at dep
      rw [(swap_distinct_installs_right_value_at_left raw left).1] at dep
      have fragment := (leaf_value_at_empty emptyDeps allow y (by simp [places]) wf).1
      change f ∈ ((extractValue s (target y)).fragment []).dependencies at dep
      rw [fragment] at dep; simp [emptyDeps] at dep
    · by_cases right : q ∈ subtreePlaces (s.base.root loc) y
      · have eq : q = y := by rw [subtree_leaf _ _ y (Or.inr rfl)] at right; exact Finset.mem_singleton.mp right
        subst q
        change f ∈ LocalDeps (post.base.root (target y).location) y at dep
        rw [(swap_distinct_installs_left_value_at_right wf raw right).1] at dep
        have fragment := (leaf_value_at_empty emptyDeps allow x (by simp [places]) wf).1
        change f ∈ ((extractValue s (target x)).fragment []).dependencies at dep
        rw [fragment] at dep; simp [emptyDeps] at dep
      · have frame := swap_preserves_local_fragments_outside_targets raw (l := loc) (q := q)
          (by simpa only [target, true_and] using left) (by simpa only [target, true_and] using right)
        rw [frame.1] at dep
        simp [LocalDeps,seed,node,emptyDeps] at dep
  · intro pkg loose; change pkg ∈ (∅ : Finset PackageId) at loose; simp at loose

theorem independent_distinct_fixed_swap_is_legal :
    StructuralSwapStep True True (seed emptyDeps false) (target x) (target y)
      (structuralSwapCandidate (seed emptyDeps false) (target x) (target y) supply) := independent_leaf_swap false

theorem fixed_swap_does_not_require_discardable :
    (seed emptyDeps false).capability loc x = false ∧ (seed emptyDeps false).capability loc y = false ∧
    StructuralSwapStep True True (seed emptyDeps false) (target x) (target y)
      (structuralSwapCandidate (seed emptyDeps false) (target x) (target y) supply) :=
  ⟨by simp [seed,cap],by simp [seed,cap],independent_distinct_fixed_swap_is_legal⟩

private def cyclicDeps (q : PlaceId) : Finset Fact :=
  if q = x then {atom y} else if q = y then {atom x} else ∅
private theorem cyclic_wf : CurrentWellFormed (seed cyclicDeps false) := by
  apply seed_wf
  intro q _ f dep
  by_cases left : q = x
  · have eq : f = atom y := by simpa [cyclicDeps,left] using dep
    subst f; exact atom_live _ _ (by simp [places])
  · by_cases right : q = y
    · have eq : f = atom x := by simpa [cyclicDeps,left,right,x,y] using dep
      subst f; exact atom_live _ _ (by simp [places])
    · simp [cyclicDeps,left,right] at dep

theorem same_place_self_dependency_is_legal :
    StructuralSwapStep True True (seed (oneDependency x x) false) (target x) (target x)
      (seed (oneDependency x x) false) := by
  have wf : CurrentWellFormed (seed (oneDependency x x) false) := by
    apply seed_wf
    intro q _ f dep
    by_cases eq : q = x
    · have same : f = atom x := by simpa [oneDependency,eq] using dep
      subst f; exact atom_live _ _ (by simp [places])
    · simp [oneDependency,eq] at dep
  exact ⟨wf,RawStructuralSwap.same ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩ trivial trivial,wf⟩

theorem cyclic_structural_swap_laundering_is_rejected (post : CurrentState) :
    ¬ StructuralSwapStep True True (seed cyclicDeps false) (target x) (target y) post := by
  classical
  intro step
  cases step.2.1 with
  | distinct raw =>
    apply swap_rejects_left_value_old_fact_dependency cyclic_wf
      (l := loc) (p := y) (q := y)
      ⟨by simp [seed],by simp [seed,layout,places]⟩
      (Finset.mem_union_right _ (target_is_affected raw.right_live))
      (target_inside y (by simp [places]) cyclicDeps false)
      ?_ ⟨raw,step.2.2⟩
    have fragment := (leaf_value_at_empty cyclicDeps false x (by simp [places]) cyclic_wf).1
    change atom y ∈ ((extractValue (seed cyclicDeps false) (target x)).fragment []).dependencies
    rw [fragment]; simp [cyclicDeps,x,y]


theorem whole_root_store_is_legal :
    StructuralStoreStep True True (before p0 (oneDependency p0 p0) (fun _ => ∅) true) (target p0) input
      (newValue p0 (oneDependency p0 p0) (fun _ => ∅) true) supply
      (structuralStoreCandidate (before p0 (oneDependency p0 p0) (fun _ => ∅) true) (target p0) input
        (newValue p0 (oneDependency p0 p0) (fun _ => ∅) true) supply) :=
  store_old_self_legal p0 (by simp [places])


private def siblingIncoming (k : List Nat) : Finset Fact := if k = [0] then {atom b} else ∅
private def siblingBefore : CurrentState := before a (oneDependency a b) siblingIncoming true
private def siblingValue : StructuredValue := newValue a (oneDependency a b) siblingIncoming true
private def siblingPost : CurrentState := structuralReplaceCandidate siblingBefore (target a) input output siblingValue supply
private theorem sibling_wf : CurrentWellFormed siblingBefore := by
  apply before_wf
  · intro q _ f dep
    by_cases same : q = a
    · have eq : f = atom b := by simpa [oneDependency,same] using dep
      subst f; exact atom_live _ _ (by simp [places])
    · simp [oneDependency,same] at dep
  · intro k _ f dep
    by_cases same : k = [0]
    · have eq : f = atom b := by simpa [siblingIncoming,same] using dep
      subst f; exact atom_live _ _ (by simp [places])
    · simp [siblingIncoming,same] at dep

private theorem a_b_disjoint : KnownDisjoint layout a b := by
  rw [KnownDisjoint,overlap_iff_prefixes (by simp [places]) (by simp [places])]
  simp [path,p0,a,b]

private theorem sibling_raw : RawStructuralReplace True True siblingBefore (target a) input output siblingValue supply siblingPost := by
  simpa [siblingBefore,siblingValue,siblingPost,a,p0] using
    raw_replace a (by simp [places]) (oneDependency a b) siblingIncoming true sibling_wf

private theorem sibling_fact_preserved : atom b ∈ StructuralLiveFacts siblingPost.base :=
  replace_preserves_disjoint_live_facts sibling_raw
    ⟨by simp [siblingBefore,before,seed,target],by simp [siblingBefore,before,seed,target,layout,places]⟩ a_b_disjoint

theorem disjoint_dependency_replace_is_legal :
    StructuralReplaceStep True True siblingBefore (target a) input output siblingValue supply siblingPost := by
  classical
  refine ⟨sibling_wf,sibling_raw,?_⟩
  apply checked_post siblingBefore siblingPost sibling_wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (affectedBy siblingBefore.base (target a)) supply sibling_raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l _; change _ ∉ insert output (Finset.erase {input} input)
    simp only [Finset.erase_singleton,Finset.mem_insert,Finset.notMem_empty,or_false]
    change (if l = loc ∧ a = p0 then input else ⟨0⟩) ≠ output
    simp [a,p0,output]
  · intro l q live f dep
    have sameLoc : l = loc := Finset.mem_singleton.mp live.1
    subst l
    change f ∈ (if loc = (target a).location ∧ q ∈ subtreePlaces (siblingBefore.base.root loc) a
      then siblingIncoming (relativePosition (siblingBefore.base.root loc) a q) else oneDependency a b q) at dep
    have atomEq : f = atom b := by
      split at dep
      · unfold siblingIncoming at dep; split at dep <;> simp_all
      · unfold oneDependency at dep; split at dep <;> simp_all
    subst f; exact sibling_fact_preserved
  · intro pkg loose
    have same : pkg = output := by simpa [siblingPost,structuralReplaceCandidate,installValue,siblingBefore,before] using loose
    subst pkg
    refine ⟨extractValue siblingBefore (target a),?_,?_,?_⟩
    · simp [siblingPost,structuralReplaceCandidate]
    · simp [siblingPost,structuralReplaceCandidate]
    · intro f dep
      rw [extract_value_dependencies sibling_wf (by simp [siblingBefore,before,seed,target])] at dep
      rcases subtree_dependency_has_local_owner dep with ⟨q,_,_,ownedDep⟩
      change f ∈ oneDependency a b q at ownedDep
      have eq : f = atom b := by unfold oneDependency at ownedDep; split at ownedDep <;> simp_all
      subst f; exact sibling_fact_preserved

theorem incoming_dependency_partition_is_preserved :
    LocalDeps (siblingPost.base.root loc) a = ∅ ∧
    LocalDeps (siblingPost.base.root loc) x = {atom b} ∧
    LocalDeps (siblingPost.base.root loc) y = ∅ ∧
    LocalDeps (siblingPost.base.root loc) p0 = ∅ := by
  classical
  have aInside := target_inside a (by simp [places]) (oneDependency a b) true
  have xInside : x ∈ subtreePlaces (siblingBefore.base.root loc) a := by
    dsimp only [siblingBefore,before]
    rw [subtree_mem _ _ _ _ (by simp [places])]; simp [places,path,p0,a,b,x]
  have yInside : y ∈ subtreePlaces (siblingBefore.base.root loc) a := by
    dsimp only [siblingBefore,before]
    rw [subtree_mem _ _ _ _ (by simp [places])]; simp [places,path,p0,a,b,x,y]
  have ancestorOutside : p0 ∉ subtreePlaces (siblingBefore.base.root loc) a := by
    dsimp only [siblingBefore,before]
    rw [subtree_mem _ _ _ _ (by simp [places])]; simp [places,path,p0,a]
  refine ⟨?_,?_,?_,?_⟩
  · change LocalDeps (siblingPost.base.root (target a).location) a = ∅
    rw [(replace_installs_new_value sibling_raw aInside).1]
    simp [siblingValue,newValue,incomingValue,siblingIncoming,relativePosition,target]
  · change LocalDeps (siblingPost.base.root (target a).location) x = {atom b}
    rw [(replace_installs_new_value sibling_raw xInside).1]
    simp [siblingValue,newValue,incomingValue,siblingIncoming,relativePosition,target,siblingBefore,before,seed,layout,path,p0,a,b,x]
  · change LocalDeps (siblingPost.base.root (target a).location) y = ∅
    rw [(replace_installs_new_value sibling_raw yInside).1]
    simp [siblingValue,newValue,incomingValue,siblingIncoming,relativePosition,target,siblingBefore,before,seed,layout,path,p0,a,b,x,y]
  · rw [(replace_preserves_local_fragments_outside_target sibling_raw (l := loc) (q := p0)
      (by simpa only [target,true_and] using ancestorOutside)).1]
    simp [LocalDeps,siblingBefore,before,seed,node,oneDependency,p0,a]


private def patchFact (s : CurrentState) (p : PlaceId) (vf : ValueFactId) : CurrentState := by
  classical
  exact { s with base := { s.base with
    root := fun l => { s.base.root l with node := fun q =>
      (if l = loc ∧ q = p then { (s.base.root l).node q with currentFact := vf } else (s.base.root l).node q) }
    usedValueFacts := insert vf s.base.usedValueFacts } }

private def patchIncarnation (s : CurrentState) (p : PlaceId) : CurrentState := by
  classical
  exact { s with base := { s.base with root := fun l => { s.base.root l with node := fun q =>
    if l = loc ∧ q = p then { (s.base.root l).node q with incarnation := ⟨999⟩ } else (s.base.root l).node q } } }

theorem missing_ancestor_invalidation_is_not_replace :
    ¬ RawStructuralReplace True True (before x emptyDeps (fun _ => ∅) true) (target x) input output
      (newValue x emptyDeps (fun _ => ∅) true) supply (patchFact (independentPost x) p0 ⟨0⟩) := by
  intro raw
  have changed : (loc,p0) ∈ affectedBy (before x emptyDeps (fun _ => ∅) true).base (target x) := by rw [affected_x]; simp
  have required := (replace_freshens_affected raw changed).1
  simp [patchFact,supply,p0] at required

theorem missing_descendant_invalidation_is_not_replace :
    ¬ RawStructuralReplace True True (before a emptyDeps (fun _ => ∅) true) (target a) input output
      (newValue a emptyDeps (fun _ => ∅) true) supply (patchFact (independentPost a) x ⟨3⟩) := by
  intro raw
  have changed : (loc,x) ∈ affectedBy (before a emptyDeps (fun _ => ∅) true).base (target a) := by rw [affected_a]; simp
  have required := (replace_freshens_affected raw changed).1
  simp [patchFact,supply,x] at required

theorem incarnation_refresh_is_not_replace :
    ¬ RawStructuralReplace True True (before x emptyDeps (fun _ => ∅) true) (target x) input output
      (newValue x emptyDeps (fun _ => ∅) true) supply (patchIncarnation (independentPost x) x) := by
  intro raw
  have required := replace_preserves_all_incarnations raw loc x
  simp [patchIncarnation,before,seed,node,x] at required

theorem same_place_swap_cannot_allocate_facts :
    ¬ RawStructuralSwap True True (seed emptyDeps false) (target x) (target x)
      (patchFact (seed emptyDeps false) x ⟨999⟩) := by
  intro raw
  have eq := swap_same_is_identity raw
  have observation := congrArg (fun s : CurrentState => ((s.base.root loc).node x).currentFact) eq
  simp [patchFact,seed,node,x] at observation

theorem ancestor_descendant_swap_is_inapplicable :
    ¬ StructuralTargetsDisjoint (seed emptyDeps false).base (target a) (target x) := by
  rintro (different|⟨_,disjoint⟩)
  · exact different rfl
  · apply disjoint
    apply Or.inr; apply Or.inl
    exact ⟨by simp [seed,layout,places,target],by simp [seed,layout,places,target],
      [0],by simp,by simp [seed,target,layout,path,p0,a,b,x]⟩

theorem previously_used_dead_fact_cannot_be_reallocated :
    let s := { (before x emptyDeps (fun _ => ∅) true).base with
      usedValueFacts := insert (⟨99⟩ : ValueFactId) (before x emptyDeps (fun _ => ∅) true).base.usedValueFacts }
    ¬ FreshStructuralFacts s (affectedBy s (target x)) (fun _ => ⟨99⟩) := by
  classical
  dsimp only
  intro allocation
  apply allocation.1 (loc,x)
  · apply target_is_affected (t := target x)
    exact ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩
  · exact Finset.mem_insert_self _ _

theorem duplicated_new_structural_fact_is_rejected :
    ¬ FreshStructuralFacts (before x emptyDeps (fun _ => ∅) true).base
      (affectedBy (before x emptyDeps (fun _ => ∅) true).base (target x)) (fun _ => ⟨999⟩) := by
  intro allocation
  have root : (loc,p0) ∈ affectedBy (before x emptyDeps (fun _ => ∅) true).base (target x) := by rw [affected_x]; simp
  have leaf : (loc,x) ∈ affectedBy (before x emptyDeps (fun _ => ∅) true).base (target x) := by rw [affected_x]; simp
  exact fresh_structural_facts_reject_aliasing allocation root leaf (by decide) rfl

private def dropFragments (v : StructuredValue) : StructuredValue :=
  { v with fragment := fun k => { v.fragment k with dependencies := ∅ } }

theorem returned_value_must_retain_child_local_dependency :
    let s := before a (oneDependency x b) (fun _ => ∅) true
    (extractValue s (target a)).fragment [0] ≠ (dropFragments (extractValue s (target a))).fragment [0] := by
  dsimp only
  have wf := one_dependency_wf a x b (by simp [places]) true
  have inside : x ∈ subtreePlaces ((before a (oneDependency x b) (fun _ => ∅) true).base.root loc) a := by
    dsimp only [before]
    rw [subtree_mem _ _ _ _ (by simp [places])]; simp [places,path,p0,a,b,x]
  have fragment := (extract_value_fragment wf (t := target a) (by simp [before,seed,target]) inside).1
  have eq : relativePosition ((before a (oneDependency x b) (fun _ => ∅) true).base.root loc) a x = [0] := by
    simp [relativePosition,before,seed,layout,path,p0,a,b,x]
  simp only [target] at fragment
  rw [eq] at fragment
  intro same
  have dependency := congrArg ValueFragment.dependencies same
  simp only [target] at dependency
  rw [fragment] at dependency
  simp [dropFragments,LocalDeps,before,seed,node,oneDependency] at dependency

theorem flattened_incoming_package_loses_child_obligation :
    (siblingValue.fragment [0]).dependencies = {atom b} ∧
    ((dropFragments siblingValue).fragment [0]).dependencies = ∅ := by
  simp [siblingValue,newValue,incomingValue,siblingIncoming,dropFragments]

theorem incoming_flattening_is_not_the_original_value :
    dropFragments siblingValue ≠ siblingValue := by
  intro eq
  have depEq := congrArg (fun v : StructuredValue => (v.fragment [0]).dependencies) eq
  rcases flattened_incoming_package_loses_child_obligation with ⟨actual,broken⟩
  rw [actual,broken] at depEq
  have := congrArg (fun fs : Finset Fact => atom b ∈ fs) depEq
  simp at this

theorem overinvalidating_sibling_rejects_an_otherwise_legal_replace :
    CurrentWellFormed siblingPost ∧ ¬ CurrentWellFormed (patchFact siblingPost b ⟨999⟩) := by
  classical
  refine ⟨disjoint_dependency_replace_is_legal.2.2,?_⟩
  intro malformed
  have old := replace_old_value_survives sibling_raw
  have oldDep : atom b ∈ (extractValue siblingBefore (target a)).dependencies := by
    rw [extract_value_dependencies sibling_wf (by simp [siblingBefore,before,seed,target])]
    exact local_deps_subset_subtree_deps (by simp [siblingBefore,before,seed,target,layout,places])
      (by simp [LocalDeps,siblingBefore,before,seed,node,oneDependency,atom,target])
  have live := malformed.structural.looseDependenciesValid output old.1 _ old.2.2 _ oldDep
  rcases live with ⟨l,lt,_,eq⟩
  have locEq : l = loc := Finset.mem_singleton.mp lt
  subst l
  simp [patchFact,b] at eq


private theorem aggregate_subtree (deps : PlaceId → Finset Fact) (allow : Bool) (p : PlaceId)
    (which : p = a ∨ p = b) :
    subtreePlaces ((seed deps allow).base.root loc) p = if p = a then {a,x,y} else {b,bx,byp} := by
  classical
  have pt : p ∈ places := by rcases which with rfl|rfl <;> simp [places]
  ext q
  rw [subtree_mem _ _ _ _ pt]
  by_cases qt : q ∈ places
  · rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases which with rfl|rfl <;> simp [path,p0,a,b,x,y,bx,byp,c,places]
  · constructor
    · intro h; exact False.elim (qt h.1)
    · intro h
      rcases which with rfl|rfl
      · change q ∈ ({a,x,y} : Finset PlaceId) at h
        simp only [Finset.mem_insert,Finset.mem_singleton] at h
        rcases h with rfl|rfl|rfl <;> simp [places] at qt
      · change q ∈ ({b,bx,byp} : Finset PlaceId) at h
        simp only [Finset.mem_insert,Finset.mem_singleton] at h
        rcases h with rfl|rfl|rfl <;> simp [places] at qt

private theorem aggregate_shape (deps : PlaceId → Finset Fact) (allow : Bool) (p : PlaceId)
    (which : p = a ∨ p = b) : (extractValue (seed deps allow) (target p)).shape = {[],[0],[1]} := by
  classical
  change (subtreePlaces ((seed deps allow).base.root loc) p).image (relativePosition _ p) = _
  rw [aggregate_subtree deps allow p which]
  rcases which with rfl|rfl <;>
    simp [relativePosition,seed,layout,path,p0,a,b,x,y,bx,byp]

private theorem swap_supply (deps : PlaceId → Finset Fact) (allow : Bool) (p q : PlaceId) :
    FreshStructuralFacts (seed deps allow).base (swapAffected (seed deps allow).base (target p) (target q)) supply := by
  classical
  constructor
  · intro key changed old
    have live : LiveNode (seed deps allow).base key.1 key.2 := by
      rcases Finset.mem_union.mp changed with left|right
      · exact (mem_affectedBy.mp left).1
      · exact (mem_affectedBy.mp right).1
    rcases Finset.mem_image.mp old with ⟨r,rt,same⟩
    rcases place_cases live.2 with eq|eq|eq|eq|eq|eq|eq|eq <;>
      rcases place_cases rt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp_all [supply,p0,a,b,x,y,bx,byp,c]
  · intro key kc other oc same
    have liveLoc : ∀ n ∈ swapAffected (seed deps allow).base (target p) (target q), n.1 = loc := by
      intro n member
      rcases Finset.mem_union.mp member with left|right
      · exact (mem_affectedBy.mp left).2.1
      · exact (mem_affectedBy.mp right).2.1
    have indices : key.2.index = other.2.index := by
      have := congrArg ValueFactId.index same; simp only [supply] at this; omega
    exact Prod.ext ((liveLoc key kc).trans (liveLoc other oc).symm) (congrArg PlaceId.mk indices)

private theorem aggregate_swap_raw (allow : Bool) :
    RawStructuralSwapDistinct True True (seed emptyDeps allow) (target a) (target b) supply
      (structuralSwapCandidate (seed emptyDeps allow) (target a) (target b) supply) := by
  constructor
  · exact ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩
  · exact ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩
  · exact Or.inr ⟨rfl,a_b_disjoint⟩
  · refine ⟨by rw [aggregate_shape _ _ a (Or.inl rfl),aggregate_shape _ _ b (Or.inr rfl)],fun _ _=>rfl⟩
  · refine ⟨by rw [aggregate_shape _ _ b (Or.inr rfl),aggregate_shape _ _ a (Or.inl rfl)],fun _ _=>rfl⟩
  · exact swap_supply _ _ _ _
  · trivial
  · trivial
  · rfl

private theorem empty_fragment (v : StructuredValue) (empty : v.dependencies = ∅)
    {k : List Nat} (kt : k ∈ v.shape) : (v.fragment k).dependencies = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f dep
  have all : f ∈ v.dependencies := Finset.mem_biUnion.mpr ⟨k,kt,dep⟩
  rw [empty] at all; exact Finset.notMem_empty f all

theorem independent_aggregate_sibling_swap_is_legal :
    StructuralSwapStep True True (seed emptyDeps false) (target a) (target b)
      (structuralSwapCandidate (seed emptyDeps false) (target a) (target b) supply) := by
  classical
  let s := seed emptyDeps false
  let post := structuralSwapCandidate s (target a) (target b) supply
  have wf : CurrentWellFormed s := seed_empty_wf false
  have raw := aggregate_swap_raw false
  refine ⟨wf,RawStructuralSwap.distinct raw,?_⟩
  apply checked_post s post wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (swapAffected s.base (target a) (target b)) supply raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l _; change _ ∉ (∅ : Finset PackageId); simp
  · intro l q live f dep
    have sameLoc : l = loc := Finset.mem_singleton.mp live.1
    subst l
    by_cases left : q ∈ subtreePlaces (s.base.root loc) a
    · change f ∈ LocalDeps (post.base.root (target a).location) q at dep
      rw [(swap_distinct_installs_right_value_at_left raw left).1] at dep
      have kt : relativePosition (s.base.root loc) a q ∈ (extractValue s (target b)).shape := by
        rw [raw.left_fits.1]; exact Finset.mem_image.mpr ⟨q,left,rfl⟩
      have empty := empty_fragment _ (empty_extract s wf b (by simp [s,seed]) (by intro q; rfl)) kt
      change f ∈ ((extractValue s (target b)).fragment (relativePosition (s.base.root loc) a q)).dependencies at dep
      rw [empty] at dep; exact False.elim (Finset.notMem_empty f dep)
    · by_cases right : q ∈ subtreePlaces (s.base.root loc) b
      · change f ∈ LocalDeps (post.base.root (target b).location) q at dep
        rw [(swap_distinct_installs_left_value_at_right wf raw right).1] at dep
        have kt : relativePosition (s.base.root loc) b q ∈ (extractValue s (target a)).shape := by
          rw [raw.right_fits.1]; exact Finset.mem_image.mpr ⟨q,right,rfl⟩
        have empty := empty_fragment _ (empty_extract s wf a (by simp [s,seed]) (by intro q; rfl)) kt
        change f ∈ ((extractValue s (target a)).fragment (relativePosition (s.base.root loc) b q)).dependencies at dep
        rw [empty] at dep; exact False.elim (Finset.notMem_empty f dep)
      · have frame := swap_preserves_local_fragments_outside_targets raw (l := loc) (q := q)
          (by simpa only [target,true_and] using left) (by simpa only [target,true_and] using right)
        rw [frame.1] at dep; simp [LocalDeps,seed,node,emptyDeps] at dep
  · intro pkg loose; change pkg ∈ (∅ : Finset PackageId) at loose; simp at loose

theorem aggregate_swap_exchanges_child_values_without_exchanging_incarnations :
    let post := structuralSwapCandidate (seed emptyDeps false) (target a) (target b) supply
    post.content loc x = bx.index ∧ post.content loc bx = x.index ∧
    ((post.base.root loc).node x).incarnation = ⟨x.index⟩ ∧
    ((post.base.root loc).node bx).incarnation = ⟨bx.index⟩ := by
  dsimp only
  have wf := seed_empty_wf false
  have raw := aggregate_swap_raw false
  have xi : x ∈ subtreePlaces ((seed emptyDeps false).base.root loc) a := by
    rw [aggregate_subtree _ _ a (Or.inl rfl)]; simp
  have bi : bx ∈ subtreePlaces ((seed emptyDeps false).base.root loc) b := by
    rw [aggregate_subtree _ _ b (Or.inr rfl)]; simp [b,a]
  have left := (swap_distinct_installs_right_value_at_left raw xi).2
  have right := (swap_distinct_installs_left_value_at_right wf raw bi).2
  have bf := (extract_value_fragment wf (t := target b) (by simp [seed,target]) bi).1
  have af := (extract_value_fragment wf (t := target a) (by simp [seed,target]) xi).1
  have relA : relativePosition ((seed emptyDeps false).base.root loc) a x = [0] := by
    simp [relativePosition,seed,layout,path,p0,a,b,x]
  have relB : relativePosition ((seed emptyDeps false).base.root loc) b bx = [0] := by
    simp [relativePosition,seed,layout,path,p0,a,b,x,y,bx]
  change _ = _ at left right
  simp only [target] at left right bf af
  rw [relA] at left af
  rw [relB] at right bf
  rw [bf] at left
  rw [af] at right
  exact ⟨left,right,swap_distinct_preserves_all_incarnations raw loc x,
    swap_distinct_preserves_all_incarnations raw loc bx⟩


theorem self_dependency_allows_same_swap_but_rejects_distinct_swap :
    StructuralSwapStep True True (seed (oneDependency x x) false) (target x) (target x)
      (seed (oneDependency x x) false) ∧
    ∀ post, ¬ StructuralSwapStep True True (seed (oneDependency x x) false) (target x) (target y) post := by
  refine ⟨same_place_self_dependency_is_legal,?_⟩
  intro post step
  have wf := same_place_self_dependency_is_legal.1
  cases step.2.1 with
  | distinct raw =>
    apply swap_rejects_left_value_old_fact_dependency wf (l := loc) (p := x) (q := y)
      ⟨by simp [seed],by simp [seed,layout,places]⟩
      (Finset.mem_union_left _ (target_is_affected raw.left_live))
      (target_inside y (by simp [places]) (oneDependency x x) false)
      ?_ ⟨raw,step.2.2⟩
    have fragment := (leaf_value_at_empty (oneDependency x x) false x (by simp [places]) wf).1
    change atom x ∈ ((extractValue (seed (oneDependency x x) false) (target x)).fragment []).dependencies
    rw [fragment]; simp [oneDependency]

theorem cyclic_candidate_without_dependency_check_is_malformed :
    RawStructuralSwapDistinct True True (seed cyclicDeps false) (target x) (target y) supply
      (structuralSwapCandidate (seed cyclicDeps false) (target x) (target y) supply) ∧
    ¬ CurrentWellFormed (structuralSwapCandidate (seed cyclicDeps false) (target x) (target y) supply) := by
  have raw := swap_leaf_raw cyclicDeps false cyclic_wf
  refine ⟨raw,?_⟩
  intro wf
  exact cyclic_structural_swap_laundering_is_rejected _ ⟨cyclic_wf,RawStructuralSwap.distinct raw,wf⟩

private def externalDeps (q : PlaceId) : Finset Fact := if q = x ∨ q = y then {atom c} else ∅
private theorem external_wf : CurrentWellFormed (seed externalDeps false) := by
  apply seed_wf
  intro q _ f dep
  have eq : f = atom c := by unfold externalDeps at dep; split at dep <;> simp_all
  subst f; exact atom_live _ _ (by simp [places])

private theorem external_unaffected :
    (loc,c) ∉ swapAffected (seed externalDeps false).base (target x) (target y) := by
  classical
  intro affected
  rcases Finset.mem_union.mp affected with left|right
  · have overlap : StructuralOverlap layout x c := (mem_affectedBy.mp left).2.2
    rw [overlap_iff_prefixes (by simp [places]) (by simp [places])] at overlap
    simp [path,p0,a,b,x,y,bx,byp,c] at overlap
  · have overlap : StructuralOverlap layout y c := (mem_affectedBy.mp right).2.2
    rw [overlap_iff_prefixes (by simp [places]) (by simp [places])] at overlap
    simp [path,p0,a,b,x,y,bx,byp,c] at overlap

theorem swap_preserves_external_disjoint_dependency_witness :
    StructuralSwapStep True True (seed externalDeps false) (target x) (target y)
      (structuralSwapCandidate (seed externalDeps false) (target x) (target y) supply) := by
  classical
  let s := seed externalDeps false
  let post := structuralSwapCandidate s (target x) (target y) supply
  have raw := swap_leaf_raw externalDeps false external_wf
  have current := swap_distinct_preserves_unaffected_current_facts raw
    (by exact ⟨by simp [seed],by simp [seed,layout,places]⟩) external_unaffected
  have sourceLive : atom c ∈ StructuralLiveFacts post.base := ⟨loc,by simp [post,structuralSwapCandidate,refreshCurrentFacts,s,seed],
    by simp [post,structuralSwapCandidate,refreshCurrentFacts,s,seed,layout,places],current⟩
  refine ⟨external_wf,RawStructuralSwap.distinct raw,?_⟩
  apply checked_post s post external_wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (swapAffected s.base (target x) (target y)) supply raw.fresh_facts (fun _ _=>rfl) rfl
  · intro l _; change _ ∉ (∅ : Finset PackageId); simp
  · intro l q live f dep
    have sameLoc : l = loc := Finset.mem_singleton.mp live.1
    subst l
    have atomEq : f = atom c := by
      by_cases left : q ∈ subtreePlaces (s.base.root loc) x
      · have eq : q = x := by rw [subtree_leaf _ _ x (Or.inl rfl)] at left; exact Finset.mem_singleton.mp left
        subst q
        change f ∈ LocalDeps (post.base.root (target x).location) x at dep
        rw [(swap_distinct_installs_right_value_at_left raw left).1] at dep
        change f ∈ ((extractValue s (target y)).fragment []).dependencies at dep
        rw [(leaf_value_at_empty externalDeps false y (by simp [places]) external_wf).1] at dep
        simpa [externalDeps] using dep
      · by_cases right : q ∈ subtreePlaces (s.base.root loc) y
        · have eq : q = y := by rw [subtree_leaf _ _ y (Or.inr rfl)] at right; exact Finset.mem_singleton.mp right
          subst q
          change f ∈ LocalDeps (post.base.root (target y).location) y at dep
          rw [(swap_distinct_installs_left_value_at_right external_wf raw right).1] at dep
          change f ∈ ((extractValue s (target x)).fragment []).dependencies at dep
          rw [(leaf_value_at_empty externalDeps false x (by simp [places]) external_wf).1] at dep
          simpa [externalDeps] using dep
        · have frame := swap_preserves_local_fragments_outside_targets raw (l := loc) (q := q)
            (by simpa only [target,true_and] using left) (by simpa only [target,true_and] using right)
          rw [frame.1] at dep
          change f ∈ externalDeps q at dep
          unfold externalDeps at dep; split at dep <;> simp_all
    subst f; exact sourceLive
  · intro pkg loose; change pkg ∈ (∅ : Finset PackageId) at loose; simp at loose


theorem third_survivor_rejects_structural_swap (post : CurrentState) :
    ¬ StructuralSwapStep True True (seed (oneDependency c x) false) (target x) (target y) post := by
  classical
  have wf : CurrentWellFormed (seed (oneDependency c x) false) := by
    apply seed_wf
    intro q _ f dep
    have eq : f = atom x := by unfold oneDependency at dep; split at dep <;> simp_all
    subst f; exact atom_live _ _ (by simp [places])
  intro step
  cases step.2.1 with
  | distinct raw =>
    apply swap_rejects_external_surviving_invalidated_dependency wf (l := loc) (p := x) (m := loc) (q := c)
      ⟨by simp [seed],by simp [seed,layout,places]⟩
      (Finset.mem_union_left _ (target_is_affected raw.left_live))
      ⟨by simp [seed],by simp [seed,layout,places]⟩ ?_ ?_ ?_ ⟨raw,step.2.2⟩
    · have outside : c ∉ subtreePlaces ((seed (oneDependency c x) false).base.root loc) x := by
        rw [subtree_leaf _ _ x (Or.inl rfl)]; simp [c,x]
      simpa only [target,true_and] using outside
    · have outside : c ∉ subtreePlaces ((seed (oneDependency c x) false).base.root loc) y := by
        rw [subtree_leaf _ _ y (Or.inr rfl)]; simp [c,y]
      simpa only [target,true_and] using outside
    · simp [LocalDeps,seed,node,oneDependency,atom]

private theorem affected_y :
    affectedBy (before y emptyDeps (fun _ => ∅) true).base (target y) = {(loc,p0),(loc,a),(loc,y)} := by
  classical
  ext key; rcases key with ⟨l,q⟩
  rw [affected_mem y (by simp [places])]
  by_cases qt : q ∈ places
  · rcases place_cases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [path,p0,a,b,x,y,bx,byp,c,loc,places]
  · constructor
    · intro h; exact False.elim (qt h.2.1)
    · intro h; simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
      rcases h with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩ <;> simp [places] at qt

theorem sibling_swap_freshens_shared_ancestors_once_and_frames_external_sibling :
    let s := seed emptyDeps false
    let post := structuralSwapCandidate s (target x) (target y) supply
    swapAffected s.base (target x) (target y) = {(loc,p0),(loc,a),(loc,x),(loc,y)} ∧
    (((post.base.root loc).node p0).currentFact = supply (loc,p0)) ∧
    (((post.base.root loc).node a).currentFact = supply (loc,a)) ∧
    (((post.base.root loc).node c).currentFact = ⟨c.index⟩) := by
  classical
  dsimp only
  have raw := swap_leaf_raw emptyDeps false (seed_empty_wf false)
  have left : affectedBy (seed emptyDeps false).base (target x) = {(loc,p0),(loc,a),(loc,x)} := affected_x
  have right : affectedBy (seed emptyDeps false).base (target y) = {(loc,p0),(loc,a),(loc,y)} := affected_y
  have support : swapAffected (seed emptyDeps false).base (target x) (target y) =
      {(loc,p0),(loc,a),(loc,x),(loc,y)} := by
    rw [swapAffected,left,right]
    ext key; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]; tauto
  refine ⟨support,?_,?_,?_⟩
  · exact (swap_distinct_creates_fresh_current_facts raw (by rw [support]; simp)).1
  · exact (swap_distinct_creates_fresh_current_facts raw (by rw [support]; simp)).1
  · rw [swap_distinct_current_fact_equation raw,support]
    simp [seed,node,p0,a,x,y,c]


private def rootDiscardableChildNot : CurrentState :=
  let s := before x emptyDeps (fun _=>∅) false
  { s with
    base := { s.base with root := fun l=>{ s.base.root l with discardable := true } }
    capability := fun _ p=>if p = p0 then true else false }

theorem root_discardability_cannot_authorize_child_store :
    CurrentWellFormed rootDiscardableChildNot ∧
    (rootDiscardableChildNot.base.root loc).discardable = true ∧
    ∀ post, ¬ RawStructuralStore True True rootDiscardableChildNot (target x) input
      (newValue x emptyDeps (fun _=>∅) false) supply post := by
  have wf := baseline_empty x false
  refine ⟨⟨⟨wf.structural.trees,wf.structural.placesUnique,wf.structural.incarnationsUnique,
    wf.structural.currentFactsUnique,wf.structural.installedUnique,wf.structural.installedNotLoose,
    wf.structural.loosePresent,wf.structural.domainsValid,wf.structural.localDependenciesValid,
    wf.structural.looseDependenciesValid,wf.structural.valueFactsRecorded,wf.structural.incarnationsRecorded,
    wf.structural.domainCarrierCoherent⟩,wf.looseStructured,?_⟩,rfl,?_⟩
  · intro l _; simp [rootDiscardableChildNot,before,seed,layout]
  · intro post; exact store_rejects_nondiscardable_target (by simp [rootDiscardableChildNot,target,p0,x])

theorem ancestor_local_dependency_is_preserved_and_rejects_replace (post : CurrentState) :
    ¬ StructuralReplaceStep True True (before x (oneDependency p0 x) (fun _=>∅) true) (target x) input output
      (newValue x (oneDependency p0 x) (fun _=>∅) true) supply post := by
  have wf := one_dependency_wf x p0 x (by simp [places]) true
  apply replace_rejects_other_surviving_invalidated_dependency wf (l:=loc) (p:=x) (m:=loc) (q:=p0)
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩
    (target_is_affected (by exact ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩))
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩
  · have outside : p0 ∉ subtreePlaces ((seed (oneDependency p0 x) true).base.root loc) x := by
      rw [subtree_leaf _ _ x (Or.inl rfl)]; simp [p0,x]
    simpa only [target,before,true_and] using outside
  · simp [LocalDeps,before,seed,node,oneDependency,atom]


theorem omitting_discardability_can_silently_lose_nondiscardable_value :
    let s := before x emptyDeps (fun _=>∅) false
    let v := newValue x emptyDeps (fun _=>∅) false
    let post := structuralStoreCandidate s (target x) input v supply
    CurrentWellFormed s ∧ s.capability loc x = false ∧ CurrentWellFormed post ∧
      ¬ RawStructuralStore True True s (target x) input v supply post := by
  classical
  dsimp only
  let s := before x emptyDeps (fun _=>∅) false
  let v := newValue x emptyDeps (fun _=>∅) false
  let post := structuralStoreCandidate s (target x) input v supply
  have wf : CurrentWellFormed s := baseline_empty x false
  refine ⟨wf,rfl,?_,nondiscardable_fixed_child_rejects_store _⟩
  apply checked_post s post wf rfl
    ⟨rfl,fun _=>rfl,fun _ _=>rfl,fun _=>rfl,fun _=>rfl,rfl,rfl,rfl,rfl⟩
    (affectedBy s.base (target x)) supply (fresh_supply _ _ _ _) (fun _ _=>rfl) rfl
  · intro l _; change _ ∉ (∅ : Finset PackageId); simp
  · intro l q _ f dep
    change f ∈ (if _ then ∅ else ∅) at dep
    split at dep <;> exact False.elim (Finset.notMem_empty f dep)
  · intro pkg loose; change pkg ∈ (∅ : Finset PackageId) at loose; simp at loose

/-- Issue #29: one nested leaf Change combines stable fixed identities, ancestor
invalidation and sibling framing in the same checked transition. -/
theorem field_change_preserves_parent_identity_and_refreshes_ancestor :
    StructuralReplaceStep True True (before x emptyDeps (fun _=>∅) true) (target x) input output
      (newValue x emptyDeps (fun _=>∅) true) supply (independentPost x) ∧
    (((independentPost x).base.root loc).node p0).incarnation = ⟨0⟩ ∧
    (((independentPost x).base.root loc).node x).incarnation = ⟨3⟩ ∧
    atom p0 ∉ StructuralLiveFacts (independentPost x).base ∧
    atom x ∉ StructuralLiveFacts (independentPost x).base ∧
    (independentPost x).content loc p0 = p0.index := by
  have raw := leaf_replace_is_legal.2.1
  have liveRoot : LiveNode (before x emptyDeps (fun _=>∅) true).base loc p0 :=
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩
  have ancestor : Ancestor layout p0 x :=
    ⟨by simp [layout,places],by simp [layout,places],[0,0],by simp,by simp [layout,path,p0,a,b,x]⟩
  refine ⟨leaf_replace_is_legal, replace_preserves_all_incarnations raw _ _,
    replace_preserves_all_incarnations raw _ _, ?_, ?_, ?_⟩
  · exact (FixedChange.field_replace_refreshes_ancestor_and_ends_old_fact
      leaf_replace_is_legal.1 raw liveRoot ancestor).2.2.2.1
  · exact replace_old_affected_facts_not_live leaf_replace_is_legal.1 raw raw.target_live
      (target_is_affected raw.target_live)
  · have outside : ¬ (loc = loc ∧ p0 ∈ subtreePlaces ((before x emptyDeps (fun _=>∅) true).base.root loc) x) := by
      change ¬ (loc = loc ∧ p0 ∈ subtreePlaces ((seed emptyDeps true).base.root loc) x)
      rw [subtree_leaf _ _ x (Or.inl rfl)]; simp [p0,x]
    exact (replace_preserves_local_fragments_outside_target raw outside).2

theorem sibling_value_and_dependency_survive_field_change :
    StructuralReplaceStep True True siblingBefore (target a) input output siblingValue supply siblingPost ∧
    siblingPost.content loc b = siblingBefore.content loc b ∧
    atom b ∈ StructuralLiveFacts siblingPost.base := by
  have frame := FixedChange.field_replace_frames_known_disjoint_value sibling_raw
    ⟨by simp [siblingBefore,before,seed,target],by simp [siblingBefore,before,seed,target,layout,places]⟩ a_b_disjoint
  exact ⟨disjoint_dependency_replace_is_legal, frame.2.1, frame.2.2.2⟩

/-- Value(parent) can be owned by a surviving disjoint sibling; owner disjointness
does not make the dependency's ancestor source disjoint from the changed field. -/
theorem surviving_parent_value_dependency_blocks_field_change :
    CurrentWellFormed (before x (oneDependency c p0) (fun _=>∅) true) ∧
    ∀ post, ¬ StructuralReplaceStep True True (before x (oneDependency c p0) (fun _=>∅) true)
      (target x) input output (newValue x (oneDependency c p0) (fun _=>∅) true) supply post := by
  have wf := one_dependency_wf x c p0 (by simp [places]) true
  refine ⟨wf, ?_⟩
  intro post
  apply FixedChange.field_replace_rejects_surviving_overlapping_dependency wf (p:=p0) (q:=c) (m:=loc)
    ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩ ?_
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩ ?_ ?_
  · change StructuralOverlap layout x p0
    exact Or.inr (Or.inr ⟨by simp [layout,places],by simp [layout,places],
      [0,0],by simp,by simp [layout,path,p0,a,b,x]⟩)
  · have outside : c ∉ subtreePlaces ((seed (oneDependency c p0) true).base.root loc) x := by
      rw [subtree_leaf _ _ x (Or.inl rfl)]; simp [c,x]
    simpa only [target,before,true_and] using outside
  · simp [LocalDeps,before,seed,node,oneDependency,atom,target]

private def coarseDeps (p : PlaceId) : Finset Fact := if p = c then {atom b,atom p0} else ∅

/-- A finite conservative larger dependency set still contains the parent blocker. -/
theorem larger_finite_dependency_set_keeps_parent_blocker :
    CurrentWellFormed (before x coarseDeps (fun _=>∅) true) ∧
    ∀ post, ¬ StructuralReplaceStep True True (before x coarseDeps (fun _=>∅) true)
      (target x) input output (newValue x coarseDeps (fun _=>∅) true) supply post := by
  classical
  have wf : CurrentWellFormed (before x coarseDeps (fun _=>∅) true) := by
    apply before_wf
    · intro q _ f dep
      by_cases owner : q = c
      · have cases : f = atom b ∨ f = atom p0 := by simpa [coarseDeps,owner] using dep
        rcases cases with rfl|rfl <;> exact atom_live _ _ (by simp [places])
      · simp [coarseDeps,owner] at dep
    · simp
  refine ⟨wf, ?_⟩
  intro post
  apply FixedChange.field_replace_dependency_superset_keeps_blocker wf (p:=p0) (q:=c) (m:=loc)
    ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩ ?_
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩ ?_ {atom b,atom p0} ?_ ?_
  · change StructuralOverlap layout x p0
    exact Or.inr (Or.inr ⟨by simp [layout,places],by simp [layout,places],
      [0,0],by simp,by simp [layout,path,p0,a,b,x]⟩)
  · have outside : c ∉ subtreePlaces ((seed coarseDeps true).base.root loc) x := by
      rw [subtree_leaf _ _ x (Or.inl rfl)]; simp [c,x]
    simpa only [target,before,true_and] using outside
  · change {atom b,atom p0} ⊆ coarseDeps c
    simp [coarseDeps]
  · simp [before,seed,node,atom,target]

theorem field_change_keeps_enclosing_root_ptr_acquirable :
    AcquireRef True True (eraseToF0 (independentPost x).base) ⟨loc,⟨0⟩⟩ ⟨0⟩ :=
  FixedChange.field_replace_allows_enclosing_root_ptr_acquisition leaf_replace_is_legal trivial trivial

/-- The exact field incarnation is live in F1 but inaccessible through F0's root-only
token. It cannot be relabeled as the root incarnation to fake a field acquisition. -/
theorem live_field_identity_cannot_be_acquired_through_root_only_erasure :
    StructuralLiveIncarnation (before x emptyDeps (fun _=>∅) true).base ⟨3⟩ ∧
    ¬ AcquireRef True True (eraseToF0 (before x emptyDeps (fun _=>∅) true).base) ⟨loc,⟨3⟩⟩ ⟨0⟩ := by
  have live : LiveNode (before x emptyDeps (fun _=>∅) true).base loc x :=
    ⟨by simp [before,seed],by simp [before,seed,layout,places]⟩
  exact ⟨live_structural_node_has_incarnation live,
    FixedChange.erased_field_incarnation_cannot_acquire_as_root (baseline_empty x true) live
      (by simp [before,seed,layout,x,p0]) True True ⟨0⟩⟩

section FieldLifecycle
open Reference FixedLifetime

private def fieldPtr : FieldPtrToken := fieldTokenAt (seed emptyDeps true) (target x)
private theorem field_current : CurrentFieldPtr (seed emptyDeps true) fieldPtr :=
  token_at_live_field_is_current ⟨by simp [seed,target],by simp [seed,target,layout,places]⟩
    (by simp [seed,target,layout,x,p0])

theorem live_nested_field_can_acquire : FieldAcquireRef True True (seed emptyDeps true) fieldPtr ⟨0⟩ :=
  current_token_can_acquire (seed_empty_wf true) field_current rfl trivial trivial

theorem field_token_rejects_wrong_path :
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with path := [9]} ⟨0⟩ :=
  acquire_rejects_wrong_path (by simp [fieldPtr,fieldTokenAt,seed,target,layout,path,p0,a,b,x])

theorem field_token_rejects_wrong_incarnation :
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with incarnation := ⟨99⟩} ⟨0⟩ :=
  acquire_rejects_wrong_incarnation (by simp [fieldPtr,fieldTokenAt,seed,target,node,x])

theorem field_token_rejects_wrong_parent_place :
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with rootPlace := a} ⟨0⟩ :=
  acquire_rejects_wrong_root_place (by simp [seed,layout,p0,a])

theorem field_token_rejects_wrong_parent_incarnation :
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with rootIncarnation := ⟨99⟩} ⟨0⟩ :=
  acquire_rejects_wrong_root_incarnation (by simp [fieldPtr,fieldTokenAt,seed,layout,node,p0])

theorem field_token_rejects_wrong_site :
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with location := ⟨99⟩} ⟨0⟩ :=
  acquire_rejects_wrong_site (l:=loc) (seed_empty_wf true)
    ⟨by simp [seed],by simp [fieldPtr,fieldTokenAt,target,seed,layout,places]⟩ (by simp [loc])

theorem field_token_rejects_retargeting_to_sibling :
    ¬ FieldAcquireRef True True (seed emptyDeps true)
      {fieldPtr with place := y, path := [0,1]} ⟨0⟩ :=
  acquire_rejects_retargeted_field (p:=x) (seed_empty_wf true)
    ⟨by simp [fieldPtr,fieldTokenAt,target,seed],by simp [seed,layout,places]⟩ rfl (by simp [y,x])

theorem field_token_rejects_wrong_domain :
    ¬ FieldAcquireRef True True (seed emptyDeps true) fieldPtr ⟨99⟩ :=
  acquire_rejects_wrong_domain (by simp [seed])

theorem current_field_token_does_not_supply_stability_or_access :
    CurrentFieldPtr (seed emptyDeps true) fieldPtr ∧
    ¬ FieldAcquireRef False True (seed emptyDeps true) fieldPtr ⟨0⟩ ∧
    ¬ FieldAcquireRef True False (seed emptyDeps true) fieldPtr ⟨0⟩ :=
  ⟨field_current, acquire_rejects_missing_stability not_false, acquire_rejects_missing_access not_false⟩

private def BrokenCurrentToken (s : CurrentState) (ptr : FieldPtrToken) : Prop :=
  (s.base.root ptr.location).layout.root = ptr.rootPlace ∧
  ((s.base.root ptr.location).node ptr.rootPlace).incarnation = ptr.rootIncarnation ∧
  (s.base.root ptr.location).layout.path ptr.place = ptr.path ∧
  ((s.base.root ptr.location).node ptr.place).incarnation = ptr.incarnation

theorem omitting_liveness_accepts_inactive_root_table_data :
    BrokenCurrentToken (seed emptyDeps true) {fieldPtr with location := ⟨99⟩} ∧
    ¬ FieldAcquireRef True True (seed emptyDeps true) {fieldPtr with location := ⟨99⟩} ⟨0⟩ :=
  ⟨⟨rfl,rfl,rfl,rfl⟩,field_token_rejects_wrong_site⟩

private theorem field_current_before : CurrentFieldPtr (before x emptyDeps (fun _=>∅) true) fieldPtr :=
  token_at_live_field_is_current ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩
    (by simp [before,seed,target,layout,x,p0])

theorem field_change_kills_value_fact_but_preserves_acquisition :
    CurrentFieldPtr (independentPost x) fieldPtr ∧
    atom x ∉ StructuralLiveFacts (independentPost x).base ∧
    FieldAcquireRef True True (independentPost x) fieldPtr ⟨0⟩ :=
  ⟨field_replace_preserves_current_token leaf_replace_is_legal.2.1 field_current_before,
    replace_old_affected_facts_not_live leaf_replace_is_legal.1 leaf_replace_is_legal.2.1
      leaf_replace_is_legal.2.1.target_live (target_is_affected leaf_replace_is_legal.2.1.target_live),
    field_replace_reacquires_with_post_evidence leaf_replace_is_legal field_current_before rfl trivial trivial⟩

theorem field_change_still_requires_new_acquisition_evidence :
    ¬ FieldAcquireRef False True (independentPost x) fieldPtr ⟨0⟩ ∧
    ¬ FieldAcquireRef True False (independentPost x) fieldPtr ⟨0⟩ :=
  ⟨acquire_rejects_missing_stability not_false,acquire_rejects_missing_access not_false⟩

theorem sibling_change_does_not_retarget_field_token :
    fieldTokenAt (independentPost y) (target x) = fieldPtr :=
  by
    have eq := field_replace_preserves_token_at (q:=target x) (independent_replace y (by simp [places])).2.1
    exact eq

theorem acquired_field_ref_cannot_launder_old_value_dependency (post : CurrentState) :
    FieldAcquireRef True True (before x (oneDependency x x) (fun _=>∅) true) fieldPtr ⟨0⟩ ∧
    ¬ StructuralReplaceStep True True (before x (oneDependency x x) (fun _=>∅) true)
      (target x) input output (newValue x (oneDependency x x) (fun _=>∅) true) supply post := by
  have wf := one_dependency_wf x x x (by simp [places]) true
  have current : CurrentFieldPtr (before x (oneDependency x x) (fun _=>∅) true) fieldPtr :=
    token_at_live_field_is_current ⟨by simp [before,seed,target],by simp [before,seed,target,layout,places]⟩
      (by simp [before,seed,target,layout,x,p0])
  have acq := current_token_can_acquire wf current rfl (stable:=True) (access:=True) trivial trivial
  refine ⟨acq, acquisition_does_not_bypass_current_dependency acq ?_⟩
  simp [fieldPtr,fieldTokenAt,target,before,seed,LocalDeps,node,oneDependency,atom]

private theorem raw_seed_end (deps : PlaceId → Finset Fact) (returned : Bool) :
    RawEndRoot True True (seed deps true) loc ⟨0⟩ returned (endCandidate (seed deps true) loc returned) :=
  ⟨⟨by simp [seed],rfl,trivial⟩,fun _=>trivial,fun _=>rfl,rfl⟩

private theorem empty_seed_safe_end (allow : Bool) (returned : Bool) :
    EndDependenciesSafe (seed emptyDeps allow) loc returned := by
  refine ⟨?_,by simp [seed],?_⟩
  · intro m p live other
    exact False.elim (other (Finset.mem_singleton.mp live.1))
  · intro yes f dep
    have empty := empty_extract (seed emptyDeps allow) (seed_empty_wf allow) p0
      (by simp [seed]) (by intro _; rfl)
    change f ∈ (extractValue (seed emptyDeps allow) (target p0)).dependencies at dep
    rw [empty] at dep
    exact False.elim (Finset.notMem_empty f dep)

theorem independent_parent_take_and_destroy_are_legal :
    EndStep True True (seed emptyDeps true) loc ⟨0⟩ true (endCandidate (seed emptyDeps true) loc true) ∧
    EndStep True True (seed emptyDeps true) loc ⟨0⟩ false (endCandidate (seed emptyDeps true) loc false) :=
  ⟨⟨seed_empty_wf true,raw_seed_end emptyDeps true,empty_seed_safe_end true true⟩,
    ⟨seed_empty_wf true,raw_seed_end emptyDeps false,empty_seed_safe_end true false⟩⟩

theorem parent_end_stales_field_token_without_changing_stored_fact :
    (∀ returned, ¬ FieldAcquireRef True True (endCandidate (seed emptyDeps true) loc returned) fieldPtr ⟨0⟩) ∧
    (∀ returned, (((endCandidate (seed emptyDeps true) loc returned).base.root loc).node x).currentFact = ⟨3⟩) ∧
    (∀ returned, ¬ StructuralLiveIncarnation (endCandidate (seed emptyDeps true) loc returned).base ⟨3⟩) :=
  ⟨fun returned=>end_rejects_old_field_acquisition (raw_seed_end emptyDeps returned) rfl,
    fun _=>rfl,fun returned=>end_ends_every_fixed_incarnation (seed_empty_wf true)
      (raw_seed_end emptyDeps returned) (p:=x) (by simp [seed,layout,places])⟩

theorem field_access_does_not_grant_parent_ending_authority :
    FieldAcquireRef True True (seed emptyDeps true) fieldPtr ⟨0⟩ ∧
    ∀ returned post, ¬ RawEndRoot False True (seed emptyDeps true) loc ⟨0⟩ returned post :=
  ⟨live_nested_field_can_acquire,fun _ _=>acquisition_does_not_mint_ending_authority live_nested_field_can_acquire⟩

private theorem root_extract_contains_old_child_dependency :
    atom x ∈ (extractValue (seed (oneDependency x x) true) (rootTarget (seed (oneDependency x x) true) loc)).dependencies := by
  have wf : CurrentWellFormed (seed (oneDependency x x) true) := by
    apply seed_wf
    intro p _ f dep
    have eq : f = atom x := by unfold oneDependency at dep; split at dep <;> simp_all
    subst f; exact atom_live _ _ (by simp [places])
  rw [extract_value_dependencies wf (by simp [seed,rootTarget])]
  change atom x ∈ SubtreeDeps ((seed (oneDependency x x) true).base.root loc) p0
  apply ancestor_subtree_deps_subset (q:=x) (root_contains_every_place tree (by simp [layout,places]))
    (local_deps_subset_subtree_deps (p:=x) (by simp [seed,layout,places]) ?_)
  simp [LocalDeps,seed,node,oneDependency]

theorem old_child_dependency_rejects_take_but_allows_destroy :
    CurrentWellFormed (seed (oneDependency x x) true) ∧
    (∀ post, ¬ EndStep True True (seed (oneDependency x x) true) loc ⟨0⟩ true post) ∧
    EndStep True False (seed (oneDependency x x) true) loc ⟨0⟩ false
      (endCandidate (seed (oneDependency x x) true) loc false) := by
  have wf : CurrentWellFormed (seed (oneDependency x x) true) := by
    apply seed_wf
    intro p _ f dep
    have eq : f = atom x := by unfold oneDependency at dep; split at dep <;> simp_all
    subst f; exact atom_live _ _ (by simp [places])
  refine ⟨wf,fun post=>take_rejects_returned_ended_fact_dependency
    (p:=x) (by simp [seed,layout,places]) root_extract_contains_old_child_dependency, wf, ?_, ?_⟩
  · exact ⟨⟨by simp [seed],rfl,trivial⟩,by simp,fun _=>rfl,rfl⟩
  · refine ⟨?_,by simp [seed],by simp⟩
    intro m p live other
    exact False.elim (other (Finset.mem_singleton.mp live.1))

theorem unchecked_take_preserves_dead_dependency_in_returned_value :
    RawEndRoot True True (seed (oneDependency x x) true) loc ⟨0⟩ true
      (endCandidate (seed (oneDependency x x) true) loc true) ∧
    ¬ CurrentWellFormed (endCandidate (seed (oneDependency x x) true) loc true) := by
  have raw := raw_seed_end (oneDependency x x) true
  refine ⟨raw,?_⟩
  intro postWF
  rcases take_returns_exact_value raw with ⟨loose,_,value⟩
  have live := postWF.structural.looseDependenciesValid _ loose _ value _ root_extract_contains_old_child_dependency
  exact end_ends_every_fixed_current_fact old_child_dependency_rejects_take_but_allows_destroy.1 raw
    (p:=x) (by simp [seed,layout,places]) live

theorem external_loose_dependency_rejects_both_parent_end_modes :
    CurrentWellFormed (before x emptyDeps (fun _=>{atom x}) true) ∧
    ∀ returned post, ¬ EndStep True True (before x emptyDeps (fun _=>{atom x}) true) loc ⟨0⟩ returned post := by
  classical
  refine ⟨incoming_dependency_wf,?_⟩
  intro returned post
  apply end_rejects_loose_ended_fact_dependency (p:=x) (pkg:=input)
    (v:=(newValue x emptyDeps (fun _=>{atom x}) true).summary)
    (by simp [before,seed,layout,places]) (by simp [before]) (by simp [before,newValue])
  change atom x ∈ (newValue x emptyDeps (fun _=>{atom x}) true).dependencies
  apply Finset.mem_biUnion.mpr
  refine ⟨[], ?_, by simp [newValue,incomingValue]⟩
  change [] ∈ (subtreePlaces ((seed emptyDeps true).base.root loc) x).image (relativePosition _ x)
  exact Finset.mem_image.mpr ⟨x,target_inside x (by simp [places]) emptyDeps true,
    by simp [relativePosition]⟩

theorem nondiscardable_root_can_be_taken_but_not_destroyed :
    EndStep True True (seed emptyDeps false) loc ⟨0⟩ true (endCandidate (seed emptyDeps false) loc true) ∧
    ∀ post, ¬ RawEndRoot True True (seed emptyDeps false) loc ⟨0⟩ false post := by
  refine ⟨⟨seed_empty_wf false,?_,empty_seed_safe_end false true⟩,?_⟩
  · exact ⟨⟨by simp [seed],rfl,trivial⟩,fun _=>trivial,by simp,rfl⟩
  · intro post raw
    have := destroy_requires_discardability raw
    cases this

theorem destroy_does_not_inherit_take_read_requirement :
    EndStep True False (seed emptyDeps true) loc ⟨0⟩ false (endCandidate (seed emptyDeps true) loc false) ∧
    ∀ post, ¬ RawEndRoot True False (seed emptyDeps true) loc ⟨0⟩ true post := by
  refine ⟨⟨seed_empty_wf true,?_,empty_seed_safe_end true false⟩,?_⟩
  · exact ⟨⟨by simp [seed],rfl,trivial⟩,by simp,fun _=>rfl,rfl⟩
  · intro post raw; exact take_requires_ordinary_read raw

private def restartedTree (returned : Bool) : CurrentState :=
  let ended := endCandidate (seed emptyDeps true) loc returned
  { ended with
    base := { ended.base with
      liveRoots := {loc}
      root := fun _ => ⟨layout,fun p=>⟨⟨100+p.index⟩,⟨200+p.index⟩,∅⟩,⟨10⟩,⟨0⟩,true⟩
      usedIncarnations := ended.base.usedIncarnations ∪ places.image (fun p=>(⟨100+p.index⟩:IncarnationId))
      usedValueFacts := ended.base.usedValueFacts ∪ places.image (fun p=>(⟨200+p.index⟩:ValueFactId)) }
    content := fun _ p=>1000+p.index }

private theorem restarted_tree_wellFormed (returned : Bool) : CurrentWellFormed (restartedTree returned) := by
  classical
  have endedWF := end_candidate_wellFormed (seed_empty_wf true) (by simp [seed]) (empty_seed_safe_end true returned)
  have oldEmpty := empty_extract (seed emptyDeps true) (seed_empty_wf true) p0 (by simp [seed]) (by intro _; rfl)
  refine ⟨?_,endedWF.looseStructured,?_⟩
  · constructor
    · intro l _; exact tree
    · intro l m p lp mp; exact (Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mp.1).symm
    · intro l p m q lp mq same
      refine ⟨(Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mq.1).symm,?_⟩
      have eq := congrArg IncarnationId.index same
      have indices : p.index = q.index := by change 100+p.index = 100+q.index at eq; omega
      exact congrArg PlaceId.mk indices
    · intro l p m q lp mq same
      refine ⟨(Finset.mem_singleton.mp lp.1).trans (Finset.mem_singleton.mp mq.1).symm,?_⟩
      have eq := congrArg ValueFactId.index same
      have indices : p.index = q.index := by change 200+p.index = 200+q.index at eq; omega
      exact congrArg PlaceId.mk indices
    · intro l lp m mp _; exact (Finset.mem_singleton.mp lp).trans (Finset.mem_singleton.mp mp).symm
    · intro l _; cases returned <;> simp [restartedTree,endCandidate,seed]
    · exact endedWF.structural.loosePresent
    · simp [restartedTree,endCandidate,seed]
    · intro l p _ f dep; exact False.elim (Finset.notMem_empty f dep)
    · intro pkg loose v data f dep
      cases returned with
      | false => simp [restartedTree,endCandidate,seed] at loose
      | true =>
        have eq : pkg = (⟨0⟩:PackageId) := by simpa [restartedTree,endCandidate,seed] using loose
        subst pkg
        have valueEq : v = (extractValue (seed emptyDeps true) (target p0)).summary := by
          apply Option.some.inj
          simpa [restartedTree,endCandidate,seed,rootTarget,layout,target] using data.symm
        rw [valueEq] at dep
        change f ∈ (extractValue (seed emptyDeps true) (target p0)).dependencies at dep
        rw [oldEmpty] at dep; exact False.elim (Finset.notMem_empty f dep)
    · intro l p live; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,live.2,rfl⟩)
    · intro l p live; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,live.2,rfl⟩)
    · exact endedWF.structural.domainCarrierCoherent
  · intro l _; rfl

private theorem restart_certificate (returned : Bool) :
    FreshTreeRestart (endCandidate (seed emptyDeps true) loc returned) (restartedTree returned) loc := by
  classical
  refine ⟨by simp [endCandidate],by simp [restartedTree],Finset.subset_union_left,?_⟩
  intro p pt used
  rcases Finset.mem_image.mp used with ⟨q,qt,same⟩
  have pt := place_cases pt
  have qt := place_cases qt
  rcases pt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases qt with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp_all [restartedTree,p0,a,b,x,y,bx,byp,c]

theorem fresh_same_site_tree_restart_does_not_revive_old_field_token :
    ∀ returned, CurrentWellFormed (restartedTree returned) ∧
      FreshTreeRestart (endCandidate (seed emptyDeps true) loc returned) (restartedTree returned) loc ∧
      ¬ FieldAcquireRef True True (restartedTree returned) fieldPtr ⟨0⟩ ∧
      FieldAcquireRef True True (restartedTree returned) (fieldTokenAt (restartedTree returned) (target x)) ⟨0⟩ := by
  intro returned
  have wf := restarted_tree_wellFormed returned
  have certificate := restart_certificate returned
  refine ⟨wf,certificate,end_then_fresh_restart_rejects_old_field_token (seed_empty_wf true)
    (raw_seed_end emptyDeps returned) field_current rfl certificate,?_⟩
  apply current_token_can_acquire wf
    (token_at_live_field_is_current ⟨by simp [restartedTree,target],by simp [restartedTree,target,layout,places]⟩
      (by simp [restartedTree,target,layout,x,p0])) rfl trivial trivial

theorem historical_child_id_reuse_cannot_satisfy_restart_certificate :
    ∀ returned, ¬ FreshTreeRestart (endCandidate (seed emptyDeps true) loc returned) (seed emptyDeps true) loc := by
  intro returned h
  apply h.2.2.2 x (by simp [seed,layout,places])
  exact Finset.mem_image.mpr ⟨x,by simp [places],rfl⟩

private theorem changed_parent_end_is_legal (returned : Bool) :
    EndStep True True (independentPost x) loc ⟨0⟩ returned (endCandidate (independentPost x) loc returned) := by
  classical
  have wf := leaf_replace_is_legal.2.2
  refine ⟨wf,⟨⟨by simp [independentPost,structuralReplaceCandidate,installValue,refreshCurrentFacts,before,seed],rfl,trivial⟩,
    fun _=>trivial,fun _=>rfl,rfl⟩,?_,?_,?_⟩
  · intro m p live other
    exact False.elim (other (Finset.mem_singleton.mp live.1))
  · intro pkg loose v data f dep
    have pkgEq : pkg = output := by simpa [independentPost,structuralReplaceCandidate,installValue,before,x,p0] using loose
    subst pkg
    have valueEq : v = (extractValue (before x emptyDeps (fun _=>∅) true) (target x)).summary := by
      apply Option.some.inj
      simpa [independentPost,structuralReplaceCandidate,ite_eq_right (show x ≠ p0 by simp [x,p0])] using data.symm
    rw [valueEq] at dep
    have empty := empty_extract (before x emptyDeps (fun _=>∅) true) leaf_replace_is_legal.1 x
      (by simp [before,seed]) (by intro _; rfl)
    change f ∈ (extractValue (before x emptyDeps (fun _=>∅) true) (target x)).dependencies at dep
    rw [empty] at dep; exact False.elim (Finset.notMem_empty f dep)
  · intro _ f dep
    have empty := empty_extract (independentPost x) wf p0
      (by simp [independentPost,structuralReplaceCandidate,installValue,refreshCurrentFacts,before,seed]) ?_
    · change f ∈ (extractValue (independentPost x) (target p0)).dependencies at dep
      rw [empty] at dep; exact False.elim (Finset.notMem_empty f dep)
    · intro q
      change (if _ then ∅ else ∅) = ∅
      split <;> rfl

theorem same_field_token_survives_change_then_stales_after_parent_end :
    FieldAcquireRef True True (independentPost x) fieldPtr ⟨0⟩ ∧
    ∀ returned, EndStep True True (independentPost x) loc ⟨0⟩ returned
      (endCandidate (independentPost x) loc returned) ∧
      ¬ FieldAcquireRef True True (endCandidate (independentPost x) loc returned) fieldPtr ⟨0⟩ :=
  ⟨field_change_kills_value_fact_but_preserves_acquisition.2.2,
    fun returned=>⟨changed_parent_end_is_legal returned,
      end_rejects_old_field_acquisition (changed_parent_end_is_legal returned).2.1 rfl⟩⟩

end FieldLifecycle

end
end NewLang.F1.Counterexample.Transition
