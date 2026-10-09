import NewLang.Adjunct.FiveRootProofs

namespace NewLang.Adjunct.FiveRoot.Counterexample
open F0 F1.Backing F1.Occupancy
noncomputable section

def world : LiveTail.WorldId := ⟨17⟩
def empty : State where
  world := world
  successes := 0
  origin := original world
  cell := fun _ => none
  owners := fun _ => []
  claim := fun _ => none
  parentFact := initialParent
  link := initialLink
  usedFacts := ∅
  usedOccurrences := ∅
  loans := ∅
  permission := fun _ => ⟨true,true⟩
  dependencies := ∅
  unknownAlias := false

theorem empty_wellFormed : WellFormed empty := by
  constructor
  · constructor
    · decide
    · intro i; simp [empty,Site.code]
    · intro i _; exact ⟨rfl,rfl⟩
    · intro i c eq; cases eq
  · constructor <;> simp [Typed,empty]
  · simp [DependenciesValid,empty]

def prefix1 := allocatePost empty .src (original world .src)
theorem allocate_src : Allocate empty .src (original world .src) :=
  ⟨empty_wellFormed,rfl,rfl,by decide,rfl⟩
theorem prefix1_wellFormed : WellFormed prefix1 := allocation_preserves_wellFormed allocate_src

def prefix2 := allocatePost prefix1 .a (original world .a)
theorem allocate_a : Allocate prefix1 .a (original world .a) :=
  ⟨prefix1_wellFormed,rfl,rfl,by decide,rfl⟩
theorem prefix2_wellFormed : WellFormed prefix2 := allocation_preserves_wellFormed allocate_a

def prefix3 := allocatePost prefix2 .b (original world .b)
theorem allocate_b : Allocate prefix2 .b (original world .b) :=
  ⟨prefix2_wellFormed,rfl,rfl,by decide,rfl⟩
theorem prefix3_wellFormed : WellFormed prefix3 := allocation_preserves_wellFormed allocate_b

def prefix4 := allocatePost prefix3 .c (original world .c)
theorem allocate_c : Allocate prefix3 .c (original world .c) :=
  ⟨prefix3_wellFormed,rfl,rfl,by decide,rfl⟩
theorem prefix4_wellFormed : WellFormed prefix4 := allocation_preserves_wellFormed allocate_c

def prefix5 := allocatePost prefix4 .dst (original world .dst)
theorem allocate_dst : Allocate prefix4 .dst (original world .dst) :=
  ⟨prefix4_wellFormed,rfl,rfl,by decide,rfl⟩
theorem prefix5_wellFormed : WellFormed prefix5 := allocation_preserves_wellFormed allocate_dst

/-- All five actual grants are present together, not assumed independent by an input table. -/
theorem five_original_live_roots : ∀ i : Site,
    Typed prefix5 i ∧ prefix5.origin i = original world i ∧
    prefix5.owners i = [.allocation (original world i),.domain (original world i)] ∧
    prefix5.claim i = some (.root ⟨0⟩ (original world i).ptr.location (full (original world i))) := by
  intro i; cases i <;> exact ⟨⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl,rfl,rfl⟩

theorem five_originals_pairwise_distinct {i j : Site} (ne : i ≠ j) :
    (prefix5.origin i).region ≠ (prefix5.origin j).region ∧
    (prefix5.origin i).ptr.incarnation ≠ (prefix5.origin j).ptr.incarnation ∧
    (prefix5.origin i).domain ≠ (prefix5.origin j).domain ∧
    (prefix5.origin i).allocation ≠ (prefix5.origin j).allocation := by
  rw [(five_original_live_roots i).2.1,(five_original_live_roots j).2.1]
  exact ⟨fun eq => ne (original_region_injective world eq),
    fun eq => ne (original_incarnation_injective world eq),
    fun eq => ne (original_domain_injective world eq),
    fun eq => ne (original_allocation_injective world eq)⟩

/-- Concrete disjoint abstract byte instances; no machine-address/ABI claim. -/
def backingWorld : F1.Backing.World where
  liveRegions := {(original world .src).region,(original world .a).region,
    (original world .b).region,(original world .c).region,(original world .dst).region}
  bytes := fun r => {⟨r.index⟩}
  access := fun _ => ⟨true,true⟩
theorem original_backings_disjoint : RegionsDisjoint backingWorld := by
  intro r _ q _ ne
  simp only [backingWorld,Finset.disjoint_singleton]
  intro eq; apply ne
  cases r; cases q; cases eq; rfl

def writeRef (s : State) (i : Site) (f : Field) : FieldRef :=
  ⟨⟨s.world,(s.origin i).ptr,(s.origin i).domain,⟨true,true⟩⟩,f,projection f⟩
def plan (n : Nat) : ChangePlan := ⟨⟨1000+10*n⟩,⟨1001+10*n⟩,⟨1002+10*n⟩,⟨100+n⟩⟩
def locator (i : Site) : LiveTail.WorldId × PtrToken := (world,(original world i).ptr)
def scopedUpdate (s : State) (i : Site) (f : Field) (target : Site) (n : Nat) : State :=
  withLoans (changePost (withLoans s {i}) i f (some (locator target)) (plan n)) ∅

private theorem update_origin (s : State) (i : Site) (f : Field) (target : Site) (n : Nat) :
    (scopedUpdate s i f target n).origin = s.origin := rfl
private theorem update_cell (s : State) (i : Site) (f : Field) (target : Site) (n : Nat) :
    (scopedUpdate s i f target n).cell = s.cell := rfl

private theorem source_update {s i f target n} (wf : WellFormed s)
    (live : Typed s i) (_source : s.origin i = original world i)
    (domain : DomainAlive s i) (perm : s.permission i = ⟨true,true⟩)
    (issued : Issued s (locator target)) (fresh : ChangeFresh s (plan n))
    (safe : ChangeGuard s i f) :
    Replace (withLoans s {i}) i f (writeRef s i f) (some (locator target)) (plan n) := by
  refine ⟨withLoans_wellFormed wf _,?_,rfl,?_,fresh,safe⟩
  · refine ⟨⟨rfl,rfl,rfl,live,domain,by simp [withLoans],?_⟩,rfl,rfl⟩
    simp [AccessLe,writeRef,withLoans,perm]
  · intro ptr eq; cases eq; exact issued

private theorem update_wellFormed {s i f target n}
    (step : Replace (withLoans s {i}) i f (writeRef s i f) (some (locator target)) (plan n)) :
    WellFormed (scopedUpdate s i f target n) :=
  withLoans_wellFormed (change_preserves_wellFormed step) _

def wired1 := scopedUpdate prefix5 .src .child .a 0
theorem source_update_1 :
    Replace (withLoans prefix5 {.src}) .src .child (writeRef prefix5 .src .child) (some (locator .a)) (plan 0) := by
  apply source_update prefix5_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired1_wellFormed : WellFormed wired1 := update_wellFormed source_update_1

def wired2 := scopedUpdate wired1 .a .prev .c 1
theorem source_update_2 :
    Replace (withLoans wired1 {.a}) .a .prev (writeRef wired1 .a .prev) (some (locator .c)) (plan 1) := by
  apply source_update wired1_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.c,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired2_wellFormed : WellFormed wired2 := update_wellFormed source_update_2

def wired3 := scopedUpdate wired2 .a .next .b 2
theorem source_update_3 :
    Replace (withLoans wired2 {.a}) .a .next (writeRef wired2 .a .next) (some (locator .b)) (plan 2) := by
  apply source_update wired2_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired3_wellFormed : WellFormed wired3 := update_wellFormed source_update_3

def wired4 := scopedUpdate wired3 .b .prev .a 3
theorem source_update_4 :
    Replace (withLoans wired3 {.b}) .b .prev (writeRef wired3 .b .prev) (some (locator .a)) (plan 3) := by
  apply source_update wired3_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired4_wellFormed : WellFormed wired4 := update_wellFormed source_update_4

def wired5 := scopedUpdate wired4 .b .next .c 4
theorem source_update_5 :
    Replace (withLoans wired4 {.b}) .b .next (writeRef wired4 .b .next) (some (locator .c)) (plan 4) := by
  apply source_update wired4_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.c,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired5_wellFormed : WellFormed wired5 := update_wellFormed source_update_5

def wired6 := scopedUpdate wired5 .c .prev .b 5
theorem source_update_6 :
    Replace (withLoans wired5 {.c}) .c .prev (writeRef wired5 .c .prev) (some (locator .b)) (plan 5) := by
  apply source_update wired5_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem wired6_wellFormed : WellFormed wired6 := update_wellFormed source_update_6

/-- Exact C-faithful source-shaped checkpoint after six checked updates. -/
theorem seven_pre_detach_relations :
    (wired6.link .src .child).payload = some (locator .a) ∧
    (wired6.link .a .prev).payload = some (locator .c) ∧
    (wired6.link .a .next).payload = some (locator .b) ∧
    (wired6.link .b .prev).payload = some (locator .a) ∧
    (wired6.link .b .next).payload = some (locator .c) ∧
    (wired6.link .c .prev).payload = some (locator .b) ∧
    (wired6.link .dst .child).payload = none := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem six_updates_preserve_all_originals :
    wired6.origin = prefix5.origin ∧ wired6.cell = prefix5.cell ∧
    wired6.owners = prefix5.owners ∧ wired6.claim = prefix5.claim := ⟨rfl,rfl,rfl,rfl⟩

/-- The sixth fresh plan resets A.next to EXACTLY the same copied address. -/
def reset := scopedUpdate wired6 .a .next .b 6
theorem same_address_reset_legal :
    Replace (withLoans wired6 {.a}) .a .next (writeRef wired6 .a .next)
      (some (locator .b)) (plan 6) := by
  apply source_update wired6_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · unfold ChangeFresh; decide
  · exact ⟨rfl,by intro d dep; change d ∈ (∅ : Finset F1.Conditional.Fact) at dep; simp at dep⟩
theorem reset_wellFormed : WellFormed reset := update_wellFormed same_address_reset_legal

theorem reset_freshens_only_next_occurrence :
    (wired6.link .a .next).payload = (reset.link .a .next).payload ∧
    (wired6.link .a .next).occurrence ≠ (reset.link .a .next).occurrence ∧
    reset.link .a .prev = wired6.link .a .prev ∧
    reset.link .a .child = wired6.link .a .child ∧
    reset.parentFact .a ≠ wired6.parentFact .a ∧
    reset.origin = wired6.origin := by
  refine ⟨?_,?_,?_,?_,?_,update_origin wired6 .a .next .b 6⟩
  · change (wired6.link .a .next).payload = some (locator .b)
    exact seven_pre_detach_relations.2.2.1
  · change (wired6.link .a .next).occurrence ≠ some (plan 6).occurrence
    have before : (wired6.link .a .next).occurrence = some (plan 2).occurrence := rfl
    rw [before]; decide
  · exact change_frames_sibling (withLoans wired6 {.a}) .a (by decide : Field.prev ≠ .next) (some (locator .b)) (plan 6)
  · exact change_frames_sibling (withLoans wired6 {.a}) .a (by decide : Field.child ≠ .next) (some (locator .b)) (plan 6)
  · change (plan 6).parent ≠ wired6.parentFact .a
    intro eq; apply same_address_reset_legal.fresh.1
    have recorded := wired6_wellFormed.fields.parentRecorded .a (five_original_live_roots .a).1
    exact eq ▸ recorded

def observedNext : State := {wired6 with dependencies := {.occurrence ⟨102⟩}}
theorem observedNext_wellFormed : WellFormed observedNext := by
  have m := wired6_wellFormed.memory
  have f := wired6_wellFormed.fields
  refine ⟨⟨m.bounded,m.allocatedPrefix,m.absent,m.present⟩,
    ⟨f.parentRecorded,f.fieldsRecorded,f.shape,f.occurrencesRecorded,f.payloadRecorded,f.occurrencesUnique⟩,?_⟩
  intro d dep; have eq : d = .occurrence ⟨102⟩ := by simpa [observedNext] using dep
  subst d; exact ⟨.a,⟨⟨.typed,true,0⟩,rfl,rfl⟩,.next,rfl⟩

theorem stale_payload_ref_rejected : ¬ Replace (withLoans observedNext {.a}) .a .next
    (writeRef observedNext .a .next) (some (locator .b)) (plan 6) :=
  occurrence_dependency_rejects_reset rfl (by simp [withLoans,observedNext,plan])

/-- Erroneously applying next's reset to all fields erases the live prev observation. -/
def observedPrev : State := {wired6 with dependencies := {.occurrence ⟨101⟩}}
def globalReset : State :=
  {reset with link := fun i f => if i = .a then reset.link .a .next else reset.link i f}
theorem global_reset_erases_sibling :
    globalReset.link .a .prev ≠ wired6.link .a .prev := by decide

private theorem no_old_occurrence_after_global : ¬ FactLive globalReset (.occurrence ⟨101⟩) := by
  rintro ⟨i,_,f,eq⟩
  cases i <;> cases f <;> simp [globalReset,reset,wired6,wired5,wired4,wired3,wired2,wired1,
    scopedUpdate,withLoans,changePost,prefix5,prefix4,prefix3,prefix2,prefix1,allocatePost,empty,
    initialLink,plan] at eq

theorem broken_global_reset_rejected :
    ¬ DependenciesValid {globalReset with dependencies := observedPrev.dependencies} := by
  intro deps; exact no_old_occurrence_after_global (deps (.occurrence ⟨101⟩) (by simp [observedPrev]))

/-- READ mode is preserved by projection, not promoted to WRITE. -/
theorem read_mode_write_rejected :
    ¬ Replace (withLoans wired6 {.a}) .a .next
      {(writeRef wired6 .a .next) with base := {(writeRef wired6 .a .next).base with mode := ⟨true,false⟩}}
      (some (locator .b)) (plan 6) := readonly_projection_cannot_write rfl

theorem swapped_field_id_rejected :
    ¬ Replace (withLoans wired6 {.a}) .a .prev (writeRef wired6 .a .next)
      (some (locator .b)) (plan 6) := wrong_projection_never_grants_replace (by decide)

theorem wrong_governing_domain_rejected :
    ¬ RootRefValid (withLoans wired6 {.a}) .a
      {(writeRef wired6 .a .next).base with domain := (original world .b).domain} := by
  intro valid; have wrong := valid.2.2.1; cases wrong

theorem unknown_alias_rejected :
    ¬ Replace {wired6 with unknownAlias := true} .a .next (writeRef wired6 .a .next)
      (some (locator .b)) (plan 6) := unknown_alias_never_grants_replace rfl

/-- Same raw branch-local numbers do not supply world-qualified dereference. -/
theorem equal_numbers_foreign_world_rejected :
    (original world .a).ptr = (original ⟨18⟩ .a).ptr ∧
    ¬ RootRefValid (withLoans wired6 {.a}) .a
      {(writeRef wired6 .a .next).base with world := ⟨18⟩} := by
  refine ⟨rfl,?_⟩; intro valid; have wrong := valid.1; cases wrong

/-- Copying a token grants no release responsibility, even if the token was issued. -/
def lostOwner : State := {prefix5 with owners := fun i => if i = .a then [] else prefix5.owners i}
theorem issued_ptr_does_not_repair_missing_owner :
    Issued lostOwner (locator .a) ∧ ¬ WellFormed lostOwner := by
  refine ⟨⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩,?_⟩
  intro wf; have own := (wf.memory.present .a ⟨.typed,true,0⟩ rfl).2.1
  simp [lostOwner,expectedOwners] at own

def duplicateOwner : State :=
  {prefix5 with owners := fun i => if i = .a then
    [.allocation (original world .a),.allocation (original world .a),.domain (original world .a)] else prefix5.owners i}
theorem duplicate_allocation_rejected : ¬ WellFormed duplicateOwner := by
  intro wf; have own := (wf.memory.present .a ⟨.typed,true,0⟩ rfl).2.1
  have count : 3 = 2 := congrArg List.length own; cases count

/-- Source-ordered explicit cleanup, every transition requires a live original
A/D pair. The fixed site lists below are the six strict source outcomes. -/
def cleanupRun : State → List Site → State
  | s,[] => s
  | s,i::rest => cleanupRun (cleanupPost s i) rest
inductive ActualCleanup : State → List Site → Prop where
  | nil (s) : ActualCleanup s []
  | cons {s i rest}
      (step : Cleanup s i (s.origin i) (s.origin i) (full (s.origin i)))
      (tail : ActualCleanup (cleanupPost s i) rest) : ActualCleanup s (i::rest)

theorem actualCleanup_preserves_wellFormed {s rest} (h : ActualCleanup s rest) (wf : WellFormed s) :
    WellFormed (cleanupRun s rest) := by
  induction h with
  | nil _ => exact wf
  | cons step tail ih => exact ih (cleanup_preserves_wellFormed step)

private theorem source_cleanup_ready {s i} (wf : WellFormed s)
    (typed : s.cell i = some ⟨.typed,true,0⟩)
    (loans : s.loans = ∅) (deps : s.dependencies = ∅) (known : s.unknownAlias = false) :
    Cleanup s i (s.origin i) (s.origin i) (full (s.origin i)) := by
  apply cleanup_available wf ⟨_,typed,rfl⟩
  refine ⟨known,by simp [loans],?_⟩
  simp [deps]

private theorem source_cleanup_cons {s i rest} (wf : WellFormed s)
    (typed : s.cell i = some ⟨.typed,true,0⟩)
    (loans : s.loans = ∅) (deps : s.dependencies = ∅) (known : s.unknownAlias = false)
    (tail : WellFormed (cleanupPost s i) → ActualCleanup (cleanupPost s i) rest) :
    ActualCleanup s (i::rest) := by
  have step := source_cleanup_ready wf typed loans deps known
  exact .cons step (tail (cleanup_preserves_wellFormed step))

/-- First failing allocation #1...#5, or all-success after the six updates. -/
def outcome : Fin 6 → State
  | ⟨0,_⟩ => empty
  | ⟨1,_⟩ => prefix1
  | ⟨2,_⟩ => prefix2
  | ⟨3,_⟩ => prefix3
  | ⟨4,_⟩ => prefix4
  | ⟨5,_⟩ => wired6

def cleanupOrder : Fin 6 → List Site
  | ⟨0,_⟩ => []
  | ⟨1,_⟩ => [.src]
  | ⟨2,_⟩ => [.a,.src]
  | ⟨3,_⟩ => [.b,.a,.src]
  | ⟨4,_⟩ => [.c,.b,.a,.src]
  | ⟨5,_⟩ => [.dst,.c,.b,.a,.src]

theorem outcome0_actual_cleanup : ActualCleanup (outcome 0) (cleanupOrder 0) := by
  exact .nil _

theorem outcome1_actual_cleanup : ActualCleanup (outcome 1) (cleanupOrder 1) := by
  change ActualCleanup prefix1 _
  have wf := prefix1_wellFormed
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  exact .nil _

theorem outcome2_actual_cleanup : ActualCleanup (outcome 2) (cleanupOrder 2) := by
  change ActualCleanup prefix2 _
  have wf := prefix2_wellFormed
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  exact .nil _

theorem outcome3_actual_cleanup : ActualCleanup (outcome 3) (cleanupOrder 3) := by
  change ActualCleanup prefix3 _
  have wf := prefix3_wellFormed
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  exact .nil _

theorem outcome4_actual_cleanup : ActualCleanup (outcome 4) (cleanupOrder 4) := by
  change ActualCleanup prefix4 _
  have wf := prefix4_wellFormed
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  exact .nil _

theorem outcome5_actual_cleanup : ActualCleanup (outcome 5) (cleanupOrder 5) := by
  change ActualCleanup wired6 _
  have wf := wired6_wellFormed
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  apply source_cleanup_cons wf rfl rfl rfl rfl
  intro wf
  exact .nil _

theorem all_six_outcomes_are_actual : ∀ n : Fin 6, ActualCleanup (outcome n) (cleanupOrder n) := by
  intro ⟨n,lt⟩
  match n with
  | 0 => exact outcome0_actual_cleanup
  | 1 => exact outcome1_actual_cleanup
  | 2 => exact outcome2_actual_cleanup
  | 3 => exact outcome3_actual_cleanup
  | 4 => exact outcome4_actual_cleanup
  | 5 => exact outcome5_actual_cleanup
  | _+6 => omega

theorem all_six_outcomes_wellFormed : ∀ n : Fin 6, WellFormed (outcome n) := by
  intro ⟨n,lt⟩
  match n with
  | 0 => exact empty_wellFormed
  | 1 => exact prefix1_wellFormed
  | 2 => exact prefix2_wellFormed
  | 3 => exact prefix3_wellFormed
  | 4 => exact prefix4_wellFormed
  | 5 => exact wired6_wellFormed
  | _+6 => omega

def finished (n : Fin 6) := cleanupRun (outcome n) (cleanupOrder n)

theorem all_six_clean_exits_wellFormed (n : Fin 6) : WellFormed (finished n) :=
  actualCleanup_preserves_wellFormed (all_six_outcomes_are_actual n) (all_six_outcomes_wellFormed n)

theorem each_success_freed_once_absent_never_granted : ∀ n : Fin 6, ∀ i : Site,
    (finished n).cell i = (if i.code < n.val then some ⟨.released,false,1⟩ else none) ∧
    (finished n).owners i = [] ∧ (finished n).claim i = none ∧
    (finished n).origin i = original world i := by
  intro ⟨n,lt⟩ i
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => cases i <;> exact ⟨rfl,rfl,rfl,rfl⟩
  | _+6 => omega

def freeCount (s : State) :=
  ((s.cell .src).map KnownCall.Cell.releases).getD 0 +
  ((s.cell .a).map KnownCall.Cell.releases).getD 0 +
  ((s.cell .b).map KnownCall.Cell.releases).getD 0 +
  ((s.cell .c).map KnownCall.Cell.releases).getD 0 +
  ((s.cell .dst).map KnownCall.Cell.releases).getD 0

theorem exact_zero_to_five_frees : ∀ n : Fin 6, freeCount (finished n) = n.val := by
  intro ⟨n,lt⟩
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 => rfl
  | _+6 => omega

/-- Failure #4 has exactly src/A/B originals. Losing B's A is not a clean failure exit. -/
def failureLostOwner : State := {prefix3 with owners := fun i => if i = .b then [] else prefix3.owners i}
theorem lost_owner_on_failure_rejected : ¬ WellFormed failureLostOwner := by
  intro wf; have own := (wf.memory.present .b ⟨.typed,true,0⟩ rfl).2.1
  simp [failureLostOwner,expectedOwners] at own

theorem wrong_domain_cannot_end : ¬ CanEnd wired6 .a (original world .b) := by
  intro step
  have eq := endRoot_requires_original_domain wired6_wellFormed step
  have eq' : original world .b = original world .a := eq
  have same := original_domain_injective world (congrArg Origin.domain eq')
  cases same

def aBeforeRelease := finalizePost (erasePost (endPost wired6 .a) .a) .a

theorem mismatched_allocation_cannot_free :
    ¬ CanRelease aBeforeRelease .a (original world .b) (full (original world .b)) := by
  intro step
  have eq : original world .b = original world .a := step.2.2.1
  have same := original_allocation_injective world (congrArg Origin.allocation eq)
  cases same

theorem full_extent_mismatch_cannot_free :
    ¬ CanRelease aBeforeRelease .a (original world .a) (full (original world .b)) := by
  intro step
  have eq : (original world .b).region = (original world .a).region := congrArg Extent.region step.2.2.2
  have same := original_region_injective world eq
  cases same

theorem deallocate_twice_rejected :
    ¬ CanRelease (cleanupPost wired6 .a) .a (original world .a) (full (original world .a)) :=
  double_release_rejected (source_cleanup_ready wired6_wellFormed rfl rfl rfl rfl)

theorem no_reloan_after_end : ¬ RootRefValid (withLoans (cleanupPost wired6 .a) {.a}) .a
    (writeRef wired6 .a .next).base := by
  intro valid
  rcases valid.2.2.2.1 with ⟨c,eq,phase⟩
  have eq' : KnownCall.Cell.mk .released false 1 = c := Option.some.inj eq
  subst c; cases phase

/-- Dangling Copy links are intentionally unchanged, and cannot dereference
released roots. Persistent provenance was never added as a blocking dependency. -/
theorem copied_links_do_not_block_explicit_cleanup :
    (finished 5).link = wired6.link ∧
    (finished 5).dependencies = ∅ ∧
    ActualCleanup wired6 [.dst,.c,.b,.a,.src] := ⟨rfl,rfl,outcome5_actual_cleanup⟩

/-- A sibling observer survives a next-field Reset. -/
theorem observedPrev_wellFormed : WellFormed observedPrev := by
  have m := wired6_wellFormed.memory
  have f := wired6_wellFormed.fields
  refine ⟨⟨m.bounded,m.allocatedPrefix,m.absent,m.present⟩,
    ⟨f.parentRecorded,f.fieldsRecorded,f.shape,f.occurrencesRecorded,f.payloadRecorded,f.occurrencesUnique⟩,?_⟩
  intro d dep; have eq : d = .occurrence ⟨101⟩ := by simpa [observedPrev] using dep
  subst d; exact ⟨.a,⟨⟨.typed,true,0⟩,rfl,rfl⟩,.prev,rfl⟩

theorem disjoint_sibling_observer_allows_reset :
    Replace (withLoans observedPrev {.a}) .a .next (writeRef observedPrev .a .next)
      (some (locator .b)) (plan 6) := by
  apply source_update observedPrev_wellFormed
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨⟨.typed,true,0⟩,rfl,rfl⟩
  · rfl
  · exact ⟨rfl,.b,⟨.typed,true,0⟩,rfl,rfl⟩
  · exact same_address_reset_legal.fresh
  · refine ⟨rfl,?_⟩
    intro d dep; have eq : d = .occurrence ⟨101⟩ := by simpa [observedPrev] using dep
    subst d
    change (wired6.link .a .next).occurrence ≠ some ⟨101⟩
    have before : (wired6.link .a .next).occurrence = some ⟨102⟩ := rfl
    rw [before]; decide

/-- Omitting the guard produces an invalid candidate: old P does not retarget. -/
theorem unguarded_reset_invalidates_survivor :
    ¬ DependenciesValid (changePost observedNext .a .next (some (locator .b)) (plan 6)) := by
  have ended := changed_old_occurrence_not_live same_address_reset_legal
    (show (wired6.link .a .next).occurrence = some ⟨102⟩ from rfl)
  intro deps
  apply ended
  exact deps (.occurrence ⟨102⟩) (by simp [changePost,observedNext])

/-- Original D-scoped stability cannot coexist with lifetime end. -/
theorem scoped_ref_blocks_end : ¬ CanEnd (withLoans wired6 {.a}) .a (original world .a) := by
  intro step; exact step.2.2.2.1 (by simp [withLoans])

/-- The initial typed claim and every later raw/empty claim share the full extent.
Capacity one is an abstract proof coordinate, NOT sizeof(H). -/
def geometry : Geometry where
  capacity := fun _ => 1
  byteAt := fun r n => ⟨r.index + 10*n⟩
  injective := by
    intro r a b eq
    have ids := congrArg AbstractByteId.index eq
    dsimp at ids; omega

theorem abstract_full_extent_footprint (o : Origin) :
    (full o).footprint geometry = {⟨o.region.index⟩} := by
  simp [full,Extent.footprint,Range.positions,Range.finish,geometry]

theorem abstract_geometry_compatible : geometry.Compatible backingWorld := by
  intro r; simp [geometry,backingWorld]

theorem original_full_extents_disjoint {i j : Site} (ne : i ≠ j) :
    Disjoint ((full (original world i)).footprint geometry)
      ((full (original world j)).footprint geometry) := by
  rw [abstract_full_extent_footprint,abstract_full_extent_footprint]
  simp only [Finset.disjoint_singleton]
  intro eq
  have ids := congrArg AbstractByteId.index eq
  apply ne
  apply site_code_injective
  dsimp [original] at ids
  omega


/-- Actual claims, including during test-end cleanup, never duplicate backing. -/
theorem live_root_and_empty_slot_never_coexist_at_a :
    wired6.claim .a = some (.root ⟨0⟩ (original world .a).ptr.location (full (original world .a))) ∧
    (endPost wired6 .a).claim .a = some (.slot ⟨0⟩ (full (original world .a))) ∧
    (erasePost (endPost wired6 .a) .a).claim .a = some (.storage (full (original world .a))) ∧
    (cleanupPost wired6 .a).claim .a = none := ⟨rfl,rfl,rfl,rfl⟩

def duplicateDomain : State :=
  {prefix5 with owners := fun i => if i = .a then
    [.allocation (original world .a),.domain (original world .a),.domain (original world .a)] else prefix5.owners i}
theorem duplicate_domain_rejected : ¬ WellFormed duplicateDomain := by
  intro wf; have own := (wf.memory.present .a ⟨.typed,true,0⟩ rfl).2.1
  have count : 3 = 2 := congrArg List.length own; cases count

theorem mismatched_domain_cannot_finalize :
    ¬ CanFinalize (erasePost (endPost wired6 .a) .a) .a (original world .b) := by
  intro step
  have eq : original world .b = original world .a := by
    simpa [erasePost,endPost,wired6,wired5,wired4,wired3,wired2,wired1,
      scopedUpdate,withLoans,changePost,prefix5,prefix4,prefix3,prefix2,prefix1,allocatePost,empty] using step.2
  have same := original_domain_injective world (congrArg Origin.domain eq)
  cases same

end
end NewLang.Adjunct.FiveRoot.Counterexample
