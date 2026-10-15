import NewLang.Adjunct.FiveRootProofs
import NewLang.Adjunct.Counterexample.FiveRoot

/-! F62: ONE finite, conditional named-call / two-normal-branch adapter.
Typed originals, scoped refs and complete dependency coverage are source-interface
inputs. This does not derive them from F59, a parser, or a production compiler.
The only memory update is the accepted FiveRoot Replace / changePost operation.
The closed body is set_next(dst, q) = replace(dst@next, Some(q)). -/
namespace NewLang.Adjunct.NamedCallJoin
open F0 (PtrToken)
open F1.Backing FiveRoot
noncomputable section

abbrev Locator := LiveTail.WorldId × PtrToken

/-- Copy data and hidden dependencies travel together. No reference is returned.
Scope dependencies are explicit, including dependencies of surviving memory. -/
structure Copy where
  value : Option Locator
  memoryDeps : Finset F1.Conditional.Fact
  scopeDeps : Finset Nat
  deriving DecidableEq

inductive FunctionName | setNext | unrelated deriving DecidableEq
inductive Phase | active | closed deriving DecidableEq

structure Arguments where
  target : Site
  destination : FieldRef
  locator : Locator
  memoryDeps : Finset F1.Conditional.Fact
  scopeDeps : Finset Nat

structure Formals where
  target : Site
  destination : FieldRef
  locator : Locator
  memoryDeps : Finset F1.Conditional.Fact
  scopeDeps : Finset Nat

/-- Full nominal target/ref/value substitution, not matching parameter types. -/
def Mapped (a : Arguments) (f : Formals) : Prop :=
  f.target = a.target ∧ f.destination = a.destination ∧ f.locator = a.locator ∧
  f.memoryDeps = a.memoryDeps ∧ f.scopeDeps = a.scopeDeps

/-- Checked interpretation of one visible body. No free effect certificate,
post invariant or source-issued authority is a premise. -/
structure Call (s : State) (name : FunctionName) (a : Arguments) (f : Formals)
    (p : ChangePlan) : Prop where
  definition : name = .setNext
  mapping : Mapped a f
  body : Replace s f.target .next f.destination (some f.locator) p

structure Input where
  memory : State
  head : Site
  tail : Site
  reader : FieldRef
  writer : FieldRef
  saved : Copy
  returnedMemoryDeps : Finset F1.Conditional.Fact
  returnedScopeDeps : Finset Nat
  scope : Nat
  survivorScopes : Finset Nat

/-- Explicit conditional source-interface PRE. Existing well-formed original
owners are checked; actual source issuance of typed roots/loans/access and the
completeness of the dependency overlay remain unproved adapters. -/
structure Entry (x : Input) : Prop where
  wf : WellFormed x.memory
  distinct : x.head ≠ x.tail
  exactlyTwo : ∀ i, Typed x.memory i ↔ i = x.head ∨ i = x.tail
  readRef : FieldRefValid x.memory x.head .next x.reader
  readMode : x.reader.base.mode.read = true
  writeRef : FieldRefValid x.memory x.tail .next x.writer
  writeMode : x.writer.base.mode.write = true
  loans : x.memory.loans = {x.head,x.tail}
  captured : x.saved.value = oldResult x.memory x.head .next
  issued : ∀ q, x.saved.value = some q → Issued x.memory q
  savedCoverage : x.saved.memoryDeps ⊆ x.memory.dependencies
  returnedCoverage : x.returnedMemoryDeps ⊆ x.memory.dependencies

def arguments (x : Input) (q : Locator) : Arguments :=
  ⟨x.tail,x.writer,q,x.saved.memoryDeps,x.saved.scopeDeps⟩
def bind (a : Arguments) : Formals :=
  ⟨a.target,a.destination,a.locator,a.memoryDeps,a.scopeDeps⟩

theorem entry_checks_distinct_original_identities {x} (entry : Entry x) :
    x.memory.origin x.head = original x.memory.world x.head ∧
    x.memory.origin x.tail = original x.memory.world x.tail ∧
    (x.memory.origin x.head).domain ≠ (x.memory.origin x.tail).domain ∧
    (x.memory.origin x.head).allocation ≠ (x.memory.origin x.tail).allocation := by
  rcases entry.readRef.1.2.2.2.1 with ⟨h,hc,ht⟩
  rcases entry.writeRef.1.2.2.2.1 with ⟨t,tc,tt⟩
  have head := (entry.wf.memory.present x.head h hc).1
  have tail := (entry.wf.memory.present x.tail t tc).1
  refine ⟨head,tail,?_,?_⟩
  · rw [head,tail]; intro eq; exact entry.distinct (original_domain_injective _ eq)
  · rw [head,tail]; intro eq; exact entry.distinct (original_allocation_injective _ eq)

theorem checked_call_constructed {x q p} (entry : Entry x)
    (someValue : x.saved.value = some q) (fresh : ChangeFresh x.memory p)
    (guard : ChangeGuard x.memory x.tail .next) :
    Call x.memory .setNext (arguments x q) (bind (arguments x q)) p := by
  refine ⟨rfl,⟨rfl,rfl,rfl,rfl,rfl⟩,entry.wf,entry.writeRef,entry.writeMode,?_,fresh,guard⟩
  intro ptr eq; cases eq; exact entry.issued q someValue

structure Output where
  memory : State
  saved : Copy
  returned : Copy
  scope : Nat
  survivorScopes : Finset Nat
  phase : Phase

def noWrite (x : Input) : Output :=
  ⟨x.memory,x.saved,⟨oldResult x.memory x.tail .next,x.returnedMemoryDeps,x.returnedScopeDeps⟩,
    x.scope,x.survivorScopes,.active⟩

def called (x : Input) (f : Formals) (p : ChangePlan) : Output :=
  ⟨changePost x.memory f.target .next (some f.locator) p,x.saved,
    ⟨oldResult x.memory f.target .next,x.returnedMemoryDeps,x.returnedScopeDeps⟩,
    x.scope,x.survivorScopes,.active⟩

/-- Exactly two normal constructors: None is no-write; Some executes the named
body on the validated formals. No abort/Unknown/control interpreter is claimed. -/
inductive Run (x : Input) (p : ChangePlan) : Output → Prop where
  | none : Entry x → x.saved.value = none → Run x p (noWrite x)
  | some {q f} : Entry x → x.saved.value = some q →
      Call x.memory .setNext (arguments x q) f p → Run x p (called x f p)

/-- Conservative join: retain BOTH possible current facts/occurrences.
All old data/dependencies and originals are common must-properties. -/
structure Joined (x : Input) (p : ChangePlan) (o : Output) : Prop where
  wf : WellFormed o.memory
  world : o.memory.world = x.memory.world
  permission : o.memory.permission = x.memory.permission
  cells : o.memory.cell = x.memory.cell
  origins : o.memory.origin = x.memory.origin
  owners : o.memory.owners = x.memory.owners
  claims : o.memory.claim = x.memory.claim
  dependencies : o.memory.dependencies = x.memory.dependencies
  loans : o.memory.loans = x.memory.loans
  saved : o.saved = x.saved
  returned : o.returned = ⟨oldResult x.memory x.tail .next,x.returnedMemoryDeps,x.returnedScopeDeps⟩
  headField : o.memory.link x.head .next = x.memory.link x.head .next
  siblings : ∀ g, g ≠ .next → o.memory.link x.tail g = x.memory.link x.tail g
  currentMay : (o.memory.link x.tail .next).currentFact ∈
    ({(x.memory.link x.tail .next).currentFact,p.field} : Finset F0.ValueFactId)
  occurrenceMay : (o.memory.link x.tail .next).occurrence ∈
    ({(x.memory.link x.tail .next).occurrence,some p.occurrence} : Finset (Option F1.Conditional.OccurrenceId))
  scopeIdentity : o.scope = x.scope
  survivingScopes : o.survivorScopes = x.survivorScopes
  active : o.phase = .active

theorem before_call_after_call_join {x p o} (run : Run x p o) : Joined x p o := by
  cases run with
  | none entry value =>
    refine ⟨entry.wf,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,rfl,rfl,rfl⟩
    · intro g other; rfl
    · simp [noWrite]
    · simp [noWrite]
  | @some q f entry value call =>
    have target : f.target = x.tail := call.mapping.1
    refine ⟨change_preserves_wellFormed call.body,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,rfl,rfl,rfl⟩
    · simp [called,target]
    · change (changePost x.memory f.target .next (some f.locator) p).link x.head .next = _
      rw [target]
      exact congrFun (change_frames_other_root x.memory entry.distinct .next (some f.locator) p).2 .next
    · intro g other
      change (changePost x.memory f.target .next (some f.locator) p).link x.tail g = _
      rw [target]; exact change_frames_sibling x.memory x.tail other _ p
    · simp [called,changePost,target]
    · simp [called,changePost,target]

theorem joined_preserves_two_originals_and_copy_dependencies {x p o}
    (entry : Entry x) (joined : Joined x p o) :
    (∀ i, Typed o.memory i ↔ i = x.head ∨ i = x.tail) ∧
    o.memory.origin x.head = x.memory.origin x.head ∧
    o.memory.origin x.tail = x.memory.origin x.tail ∧
    (∀ d ∈ o.saved.memoryDeps, FactLive o.memory d) ∧
    (∀ d ∈ o.returned.memoryDeps, FactLive o.memory d) := by
  refine ⟨?_,congrFun joined.origins _,congrFun joined.origins _,?_,?_⟩
  · intro i; unfold Typed; rw [joined.cells]; exact entry.exactlyTwo i
  · intro d member; apply joined.wf.dependencies d
    rw [joined.dependencies]; apply entry.savedCoverage
    simpa [joined.saved] using member
  · intro d member; apply joined.wf.dependencies d
    rw [joined.dependencies]; apply entry.returnedCoverage
    simpa [joined.returned] using member

theorem joined_saved_copy_remains_exact {x p o} (entry : Entry x) (joined : Joined x p o) :
    o.saved.value = oldResult o.memory x.head .next ∧
    o.saved.memoryDeps = x.saved.memoryDeps ∧ o.saved.scopeDeps = x.saved.scopeDeps := by
  refine ⟨?_,congrArg Copy.memoryDeps joined.saved,congrArg Copy.scopeDeps joined.saved⟩
  rw [joined.saved,entry.captured]
  unfold oldResult; rw [joined.headField]

/-- Current point validity survives while the same caller scope is active;
this is neither a new Domain grant nor ref validity after lexical close. -/
theorem joined_keeps_original_write_ref {x p o} (entry : Entry x) (joined : Joined x p o) :
    FieldRefValid o.memory x.tail .next x.writer := by
  simpa only [FieldRefValid,RootRefValid,Typed,DomainAlive,joined.world,joined.origins,
    joined.cells,joined.loans,joined.permission] using entry.writeRef

theorem call_resets_old_occurrence {x : Input} {q f p old}
    (call : Call x.memory .setNext (arguments x q) f p)
    (oldAt : (x.memory.link x.tail .next).occurrence = some old) :
    ¬ FactLive (called x f p).memory (.occurrence old) ∧ p.occurrence ≠ old := by
  have same : f.target = x.tail := call.mapping.1
  have atFormal : (x.memory.link f.target .next).occurrence = some old := same ▸ oldAt
  exact ⟨changed_old_occurrence_not_live call.body atFormal,
    (some_to_some_starts_fresh_occurrence call.body atFormal).2.1⟩

def closed (o : Output) : Output :=
  {o with memory := withLoans o.memory ∅,phase := .closed}

/-- One explicit lexical close; complete scope-dependency coverage is a source
obligation. It preserves all copies, never erases dependency fields. -/
structure Finish (before after : Output) : Prop where
  active : before.phase = .active
  nonescape : before.scope ∉ before.saved.scopeDeps ∪ before.returned.scopeDeps ∪ before.survivorScopes
  result : after = closed before

theorem finish_preserves_and_ends_refs {x p o after}
    (joined : Joined x p o) (finish : Finish o after) :
    WellFormed after.memory ∧ after.memory.cell = x.memory.cell ∧
    after.memory.origin = x.memory.origin ∧ after.memory.owners = x.memory.owners ∧
    after.memory.claim = x.memory.claim ∧ after.saved = o.saved ∧ after.returned = o.returned ∧
    after.memory.dependencies = x.memory.dependencies ∧
    (∀ i r, ¬ RootRefValid after.memory i r) := by
  rw [finish.result]
  refine ⟨withLoans_wellFormed joined.wf _,joined.cells,joined.origins,joined.owners,joined.claims,
    rfl,rfl,joined.dependencies,?_⟩
  intro i r valid
  have absent := valid.2.2.2.2.2.1
  exact Finset.notMem_empty i absent

theorem finish_cannot_repeat {o after again} (finish : Finish o after) : ¬ Finish after again := by
  intro second; rw [finish.result] at second
  cases second.active

theorem wrong_actual_formal_root_rejected {s a f p name}
    (wrong : f.target ≠ a.target) : ¬ Call s name a f p :=
  fun call => wrong call.mapping.1

theorem wrong_actual_formal_ref_rejected {s a f p name}
    (wrong : f.destination ≠ a.destination) : ¬ Call s name a f p :=
  fun call => wrong call.mapping.2.1

theorem erased_formal_dependency_rejected {s a f p name}
    (lost : f.memoryDeps ≠ a.memoryDeps) : ¬ Call s name a f p :=
  fun call => lost call.mapping.2.2.2.1

theorem wrong_field_rejected {s a f p name} (wrong : f.destination.field ≠ .next) :
    ¬ Call s name a f p := fun call => wrong call.body.ref.2.1

theorem stale_target_incarnation_rejected {s a f p name}
    (stale : f.destination.base.ptr.incarnation ≠ (s.origin f.target).ptr.incarnation) :
    ¬ Call s name a f p := by
  intro call
  exact stale (congrArg PtrToken.incarnation call.body.ref.1.2.1)

theorem surviving_dependency_conflict_rejected {s a f p name d}
    (survives : d ∈ s.dependencies) (conflict : Affected s f.target .next d) :
    ¬ Call s name a f p := fun call => call.body.guard.2 d survives conflict

theorem invented_root_rejected {x p o} (invented : o.memory.cell ≠ x.memory.cell) :
    ¬ Run x p o := fun run => invented (before_call_after_call_join run).cells

theorem overwritten_old_copy_rejected {x p o}
    (changed : o.returned.value ≠ oldResult x.memory x.tail .next) : ¬ Run x p o := by
  intro run; apply changed
  exact congrArg Copy.value (before_call_after_call_join run).returned

theorem escaped_survivor_ref_rejected {o after} (escape : o.scope ∈ o.survivorScopes) :
    ¬ Finish o after := fun finish => finish.nonescape (Finset.mem_union_right _ escape)

theorem escaped_return_ref_rejected {o after} (escape : o.scope ∈ o.returned.scopeDeps) :
    ¬ Finish o after := fun finish => finish.nonescape
      (Finset.mem_union_left _ (Finset.mem_union_right _ escape))

theorem read_mode_cannot_call_write {s a f p name}
    (readOnly : f.destination.base.mode.write = false) : ¬ Call s name a f p := by
  intro call; have allowed := call.body.write; rw [readOnly] at allowed; cases allowed

namespace Witness
open FiveRoot.Counterexample

def opened := withLoans prefix2 {.src,.a}

theorem ref_valid {s : State} {i : Site} (typed : Typed s i) (domain : DomainAlive s i)
    (loan : i ∈ s.loans) (permission : s.permission i = ⟨true,true⟩) :
    FieldRefValid s i .next (writeRef s i .next) := by
  refine ⟨⟨rfl,rfl,rfl,typed,domain,loan,?_⟩,rfl,rfl⟩
  simp [writeRef,AccessLe,permission]

theorem seed_replace : Replace opened .a .next (writeRef opened .a .next)
    (some (locator .src)) (plan 0) := by
  refine ⟨withLoans_wellFormed prefix2_wellFormed _,?_,rfl,?_,by unfold ChangeFresh; decide,?_⟩
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.src,⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨rfl,by intro d dep; exact False.elim (Finset.notMem_empty _ dep)⟩

def seed := changePost opened .a .next (some (locator .src)) (plan 0)
theorem seed_wf : WellFormed seed := change_preserves_wellFormed seed_replace

theorem head_replace : Replace seed .src .next (writeRef seed .src .next)
    (some (locator .a)) (plan 1) := by
  refine ⟨seed_wf,?_,rfl,?_,by unfold ChangeFresh; decide,?_⟩
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · intro ptr eq; cases eq; exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · exact ⟨rfl,by intro d dep; exact False.elim (Finset.notMem_empty _ dep)⟩

def headSeed := changePost seed .src .next (some (locator .a)) (plan 1)
def atom : F1.Conditional.Fact := .fixed (.domainLive (original world .src).domain)
def observed (s : State) : State := {s with dependencies := {atom}}

theorem observed_wf {s : State} (wf : WellFormed s) (live : FactLive s atom) :
    WellFormed (observed s) := by
  refine ⟨⟨wf.memory.bounded,wf.memory.allocatedPrefix,wf.memory.absent,wf.memory.present⟩,
    ⟨wf.fields.parentRecorded,wf.fields.fieldsRecorded,wf.fields.shape,
      wf.fields.occurrencesRecorded,wf.fields.payloadRecorded,wf.fields.occurrencesUnique⟩,?_⟩
  intro d member
  have eq : d = atom := Finset.mem_singleton.mp member
  subst d; exact live

def input (s : State) : Input :=
  ⟨s,.src,.a,writeRef s .src .next,writeRef s .a .next,
    ⟨oldResult s .src .next,{atom},∅⟩,{atom},∅,77,∅⟩
def noneInput := input (observed seed)
def someInput := input (observed headSeed)

theorem none_entry : Entry noneInput := by
  refine ⟨observed_wf seed_wf ?_,by decide,?_,?_,rfl,?_,rfl,rfl,rfl,?_,?_,?_⟩
  · exact ⟨.src,⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl⟩
  · intro i; cases i <;>
      simp [noneInput,input,observed,seed,opened,prefix2,prefix1,empty,allocatePost,withLoans,changePost,Typed]
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · intro q impossible; cases impossible
  · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _

theorem some_entry : Entry someInput := by
  refine ⟨observed_wf (change_preserves_wellFormed head_replace) ?_,by decide,?_,?_,rfl,?_,rfl,rfl,rfl,?_,?_,?_⟩
  · exact ⟨.src,⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl⟩
  · intro i; cases i <;>
      simp [someInput,input,observed,headSeed,seed,opened,prefix2,prefix1,empty,allocatePost,withLoans,changePost,Typed]
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · exact ref_valid ⟨⟨.typed,true,0⟩,rfl,rfl⟩ ⟨⟨.typed,true,0⟩,rfl,rfl⟩ (by decide) rfl
  · intro q eq
    have same : locator .a = q := Option.some.inj eq
    subst q; exact ⟨rfl,.a,⟨.typed,true,0⟩,rfl,rfl⟩
  · exact Finset.Subset.refl _
  · exact Finset.Subset.refl _

def formals := bind (arguments someInput (locator .a))
def someOutput := called someInput formals (plan 2)
def noneOutput := noWrite noneInput

theorem some_call : Call someInput.memory .setNext (arguments someInput (locator .a)) formals (plan 2) := by
  apply checked_call_constructed some_entry rfl (by unfold ChangeFresh; decide)
  refine ⟨rfl,?_⟩
  intro d member
  have eq : d = atom := Finset.mem_singleton.mp member
  subst d; simp [Affected,atom]

theorem some_normal_path : Run someInput (plan 2) someOutput :=
  Run.some some_entry rfl some_call
theorem none_normal_path : Run noneInput (plan 2) noneOutput :=
  Run.none none_entry rfl

theorem two_normal_paths_join : Joined someInput (plan 2) someOutput ∧
    Joined noneInput (plan 2) noneOutput ∧
    someOutput.returned = noneOutput.returned ∧
    someOutput.returned.value = some (locator .src) ∧
    someOutput.saved.value = some (locator .a) ∧
    someOutput.memory.dependencies = {atom} ∧ noneOutput.memory.dependencies = {atom} ∧
    (someOutput.memory.link .a .next).occurrence ≠ (noneOutput.memory.link .a .next).occurrence :=
  ⟨before_call_after_call_join some_normal_path,before_call_after_call_join none_normal_path,
    rfl,rfl,rfl,rfl,rfl,by decide⟩

theorem some_scope_finishes : Finish someOutput (closed someOutput) :=
  ⟨rfl,by decide,rfl⟩
theorem none_scope_finishes : Finish noneOutput (closed noneOutput) :=
  ⟨rfl,by decide,rfl⟩

theorem old_some_occurrence_cannot_return_as_current :
    ¬ FactLive someOutput.memory (.occurrence ⟨100⟩) ∧ (plan 2).occurrence ≠ ⟨100⟩ :=
  call_resets_old_occurrence some_call rfl

/-- Both concrete normal exits inhabit one conservative join, although their
new current values/facts/occurrences differ. No intersection erases blockers. -/
theorem finite_normal_join (o : Output) (normal : o = noneOutput ∨ o = someOutput) :
    WellFormed o.memory ∧ o.memory.owners = seed.owners ∧ o.memory.origin = seed.origin ∧
    o.returned.value = some (locator .src) ∧ o.returned.memoryDeps = {atom} ∧
    (o.memory.link .a .next).payload ∈
      ({some (locator .src),some (locator .a)} : Finset (Option Locator)) ∧
    (o.memory.link .a .next).currentFact ∈
      ({(plan 0).field,(plan 2).field} : Finset F0.ValueFactId) ∧
    (o.memory.link .a .next).occurrence ∈
      ({some (plan 0).occurrence,some (plan 2).occurrence} : Finset (Option F1.Conditional.OccurrenceId)) ∧
    FactLive o.memory atom := by
  rcases normal with rfl | rfl
  · exact ⟨two_normal_paths_join.2.1.wf,rfl,rfl,rfl,rfl,by decide,by decide,by decide,
      ⟨.src,⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl⟩⟩
  · exact ⟨two_normal_paths_join.1.wf,rfl,rfl,rfl,rfl,by decide,by decide,by decide,
      ⟨.src,⟨⟨.typed,true,0⟩,rfl,rfl⟩,rfl⟩⟩

theorem both_normal_paths_close_preserving_originals :
    WellFormed (closed someOutput).memory ∧ WellFormed (closed noneOutput).memory ∧
    (closed someOutput).memory.owners = seed.owners ∧
    (closed noneOutput).memory.owners = seed.owners ∧
    (closed someOutput).saved = someInput.saved ∧
    (closed someOutput).returned = someOutput.returned ∧
    (∀ i r, ¬ RootRefValid (closed someOutput).memory i r) ∧
    (∀ i r, ¬ RootRefValid (closed noneOutput).memory i r) := by
  have someClosed := finish_preserves_and_ends_refs two_normal_paths_join.1 some_scope_finishes
  have noneClosed := finish_preserves_and_ends_refs two_normal_paths_join.2.1 none_scope_finishes
  exact ⟨someClosed.1,noneClosed.1,rfl,rfl,rfl,rfl,
    someClosed.2.2.2.2.2.2.2.2,noneClosed.2.2.2.2.2.2.2.2⟩

def swapped : Formals := {formals with target := .src,destination := someInput.reader}
theorem swapped_original_actual_rejected :
    ¬ Call someInput.memory .setNext (arguments someInput (locator .a)) swapped (plan 2) :=
  wrong_actual_formal_root_rejected (by decide)

def staleArguments : Arguments := {arguments someInput (locator .a) with
  destination := {someInput.writer with base := {someInput.writer.base with
    ptr := {someInput.writer.base.ptr with incarnation := ⟨99⟩}}}}
theorem stale_actual_rejected :
    ¬ Call someInput.memory .setNext staleArguments (bind staleArguments) (plan 2) :=
  stale_target_incarnation_rejected (by decide)

def wrongFieldArguments : Arguments := {arguments someInput (locator .a) with
  destination := {someInput.writer with field := .prev}}
theorem wrong_field_actual_rejected :
    ¬ Call someInput.memory .setNext wrongFieldArguments (bind wrongFieldArguments) (plan 2) :=
  wrong_field_rejected (by decide)

def lostDependencyFormals : Formals := {formals with memoryDeps := ∅}
theorem dropped_hidden_dependency_rejected :
    ¬ Call someInput.memory .setNext (arguments someInput (locator .a)) lostDependencyFormals (plan 2) :=
  erased_formal_dependency_rejected (by decide)

def conflictMemory : State := {someInput.memory with
  dependencies := insert (.occurrence ⟨100⟩) someInput.memory.dependencies}
theorem conflict_entry_memory_wellFormed : WellFormed conflictMemory := by
  have wf := some_entry.wf
  refine ⟨⟨wf.memory.bounded,wf.memory.allocatedPrefix,wf.memory.absent,wf.memory.present⟩,
    ⟨wf.fields.parentRecorded,wf.fields.fieldsRecorded,wf.fields.shape,
      wf.fields.occurrencesRecorded,wf.fields.payloadRecorded,wf.fields.occurrencesUnique⟩,?_⟩
  intro d member
  rcases Finset.mem_insert.mp member with rfl | old
  · exact ⟨.a,⟨⟨.typed,true,0⟩,rfl,rfl⟩,.next,rfl⟩
  · exact wf.dependencies d old

theorem surviving_old_occurrence_rejected :
    ¬ Call conflictMemory .setNext (arguments someInput (locator .a)) formals (plan 2) := by
  apply surviving_dependency_conflict_rejected (d := .occurrence ⟨100⟩)
  · exact Finset.mem_insert_self _ _
  · exact rfl

def inventedOutput : Output := {someOutput with memory := {someOutput.memory with
  cell := fun i => if i = .dst then some ⟨.typed,true,0⟩ else someOutput.memory.cell i}}
theorem invented_third_root_rejected : ¬ Run someInput (plan 2) inventedOutput := by
  apply invented_root_rejected
  intro same; have impossible := congrFun same .dst; cases impossible

def overwrittenOutput : Output := {someOutput with returned := {someOutput.returned with value := none}}
theorem overwritten_old_some_copy_rejected : ¬ Run someInput (plan 2) overwrittenOutput :=
  overwritten_old_copy_rejected (by decide)

theorem double_scope_end_rejected : ¬ Finish (closed someOutput) (closed (closed someOutput)) :=
  finish_cannot_repeat some_scope_finishes

def escapingOutput : Output := {someOutput with survivorScopes := {77}}
theorem surviving_ref_escape_rejected : ¬ Finish escapingOutput (closed escapingOutput) :=
  escaped_survivor_ref_rejected (by decide)

end Witness

end
end NewLang.Adjunct.NamedCallJoin
