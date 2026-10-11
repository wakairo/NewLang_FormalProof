import NewLang.Adjunct.FreshDomainWitness
import NewLang.F2.Model

/-! Issue #59: ONE proof-only, pre-typed Domain-value ordinary read loan.
This is a NEW guarded source abstraction, not selected F0/F1/F2 acquisition.
F2 ScopeClosed is reused as a syntactic dependency checker in a slice with
no enclosing loop/loan scopes. Its iteration tag is NOT a runtime loan id.
No object location, typed root, ptr or incarnation is manufactured. -/
namespace NewLang.Adjunct.DomainValueReadLoan
open F0 F1.Backing F1.Occupancy OneBackingSlotSource FreshDomainRich
noncomputable section

structure ScopeId where
  index : Nat
  deriving DecidableEq

/-- Ordinary Copy read capability; it contains no ownership or ending authority. -/
structure Token where
  domain : DomainId
  value : Nat
  scope : ScopeId
  deriving DecidableEq

inductive Phase | ready | active | closed deriving DecidableEq
inductive Mode | ordinaryRead | exclusiveRead deriving DecidableEq

structure ScopeHistory where
  next : Nat
  used : Finset ScopeId
  below : ∀ q ∈ used, q.index < next

structure State where
  source : FreshDomainSource.State
  nextScope : Nat
  usedScopes : Finset ScopeId
  phase : Phase
  active : Option Token

structure WellFormed (c : Context) (s : State) : Prop where
  sourceWF : FreshDomainSource.SourceWF c s.source
  history : ∀ q ∈ s.usedScopes, q.index < s.nextScope
  shape : s.phase = .active ↔ ∃ t, s.active = some t
  recorded : ∀ t, s.active = some t → t.scope ∈ s.usedScopes
  available : ∀ t, s.active = some t → (t.domain,t.value) ∈ s.source.available

def start (source : FreshDomainSource.State) (h : ScopeHistory) : State :=
  ⟨source,h.next,h.used,.ready,none⟩

def makeToken (s : State) (d : DomainId) (v : Nat) : Token := ⟨d,v,⟨s.nextScope⟩⟩
def beginPost (s : State) (d : DomainId) (v : Nat) : State :=
  {s with
    nextScope := s.nextScope+1
    usedScopes := insert ⟨s.nextScope⟩ s.usedScopes
    phase := .active
    active := some (makeToken s d v)}

/-- Checked direct-local acquisition. No favorable token/certificate in PRE.
Only one grant is investigated; this is not a ban on other canonical read loans. -/
structure Begin (c : Context) (s : State) (d : DomainId) (v : Nat) (mode : Mode)
    (token : Token) (post : State) : Prop where
  before : WellFormed c s
  ready : s.phase = .ready
  available : (d,v) ∈ s.source.available
  readOnly : mode = .ordinaryRead
  token_eq : token = makeToken s d v
  post_eq : post = beginPost s d v

/-- Source operand classification is explicit; a Copy ptr is not a Domain local.
This is not a proof of the compiler's AST/type classification. -/
inductive Operand where
  | domainLocal : DomainId → Nat → Operand
  | copyPointer : PtrToken → Operand

inductive RequestBegin (c : Context) (s : State) (mode : Mode) (t : Token) (post : State) : Operand → Prop where
  | local (d v) : Begin c s d v mode t post → RequestBegin c s mode t post (.domainLocal d v)

theorem copy_pointer_request_rejected (c s mode t post p) :
    ¬ RequestBegin c s mode t post (.copyPointer p) := by intro h; cases h

def Current (s : State) (t : Token) : Prop := s.active = some t
def EvidenceFor (s : State) (t : Token) (d : DomainId) : Prop := Current s t ∧ t.domain = d

/-- Explicit NEW source guard supplying F0's previously external permission.
It is not derived from rich WellFormed alone. No ending operation is defined. -/
def Unborrowed (s : State) (d : DomainId) : Prop :=
  ∀ t, Current s t → t.domain ≠ d
def CanConsume (s : State) (d : DomainId) (v : Nat) : Prop :=
  (d,v) ∈ s.source.available ∧ Unborrowed s d

def Complete (s : State) : Prop := s.phase = .closed ∧ s.active = none

/-- Explicit tag adapter for the pure F2 checker, not an F2 loop transition. -/
def scopeTag (q : ScopeId) : F2.Dependency := .iteration ⟨q.index⟩

/-- Closed finite value trees compute transitive containment, including Copies.
No arbitrary source AST, memory graph or callable evaluation is asserted here. -/
inductive Value where
  | unit
  | stable : Token → Value
  | pair : Value → Value → Value
  deriving DecidableEq

def deps : Value → Finset F2.Dependency
  | .unit => ∅
  | .stable t => {scopeTag t.scope,.externalFact (.domainLive t.domain)}
  | .pair a b => deps a ∪ deps b

def Valid (s : State) : Value → Prop
  | .unit => True
  | .stable t => Current s t
  | .pair a b => Valid s a ∧ Valid s b

def survivorsDeps : List Value → Finset F2.Dependency
  | [] => ∅
  | x :: xs => deps x ∪ survivorsDeps xs

structure Boundary where
  result : Value
  survivors : List Value
  evaluations : Nat

def exitDeps (b : Boundary) : Finset F2.Dependency := deps b.result ∪ survivorsDeps b.survivors
def endPost (s : State) : State := {s with phase := .closed, active := none}

/-- Exactly-once evaluation and full finite surviving-value inspection are
explicit source obligations. The body cannot mutate the frozen owner/rich frame.
Output is the unchanged boundary, not a dependency-erased replacement. -/
structure End (c : Context) (s : State) (t : Token) (b : Boundary)
    (post : State) (output : Boundary) : Prop where
  before : WellFormed c s
  current : Current s t
  once : b.evaluations = 1
  resultValid : Valid s b.result
  survivorsValid : ∀ x ∈ b.survivors, Valid s x
  scopeClosed : F2.ScopeClosed (exitDeps b)
  post_eq : post = endPost s
  output_eq : output = b

theorem start_wellFormed {c source} (wf : FreshDomainSource.SourceWF c source) (h : ScopeHistory) :
    WellFormed c (start source h) := by
  refine ⟨wf,h.below,?_,?_,?_⟩
  · simp [start]
  · intro t impossible; simp [start] at impossible
  · intro t impossible; simp [start] at impossible

theorem fresh_scope {c s} (wf : WellFormed c s) : (⟨s.nextScope⟩ : ScopeId) ∉ s.usedScopes := by
  intro reused; have impossible := wf.history ⟨s.nextScope⟩ reused
  exact Nat.lt_irrefl _ impossible

theorem begin_wellFormed {c s d v} (wf : WellFormed c s)
    (available : (d,v) ∈ s.source.available) : WellFormed c (beginPost s d v) := by
  refine ⟨wf.sourceWF,?_,?_,?_,?_⟩
  · intro q member
    simp only [beginPost,Finset.mem_insert] at member
    rcases member with rfl | old
    · simp [beginPost]
    · have := wf.history q old; change q.index < s.nextScope+1; omega
  · simp [beginPost]
  · intro t eq; simp only [beginPost,Option.some.injEq] at eq; subst t
    simp [beginPost,makeToken]
  · intro t eq; simp only [beginPost,Option.some.injEq] at eq; subst t; exact available

theorem acquisition_constructed {c s d v} (wf : WellFormed c s) (ready : s.phase = .ready)
    (available : (d,v) ∈ s.source.available) :
    Begin c s d v .ordinaryRead (makeToken s d v) (beginPost s d v) ∧
    WellFormed c (beginPost s d v) ∧ Current (beginPost s d v) (makeToken s d v) ∧
    (makeToken s d v).scope ∉ s.usedScopes ∧ (beginPost s d v).source = s.source :=
  ⟨⟨wf,ready,available,rfl,rfl,rfl⟩,begin_wellFormed wf available,rfl,fresh_scope wf,rfl⟩

theorem current_preserves_original_available {c s t} (wf : WellFormed c s) (h : Current s t) :
    (t.domain,t.value) ∈ s.source.available ∧ t.scope ∈ s.usedScopes :=
  ⟨wf.available t h,wf.recorded t h⟩

theorem current_is_one_grant {s t u} (a : Current s t) (b : Current s u) : t = u :=
  Option.some.inj (a.symm.trans b)

theorem original_nonCopy_domain_still_unique {c s t v} (wf : WellFormed c s)
    (token : Current s t) (other : (t.domain,v) ∈ FreshDomainSource.current s.source) : v = t.value :=
  wf.sourceWF.domainUnique _ _ _ other (Finset.mem_union_left _ (wf.available t token))

theorem active_blocks_original_consume {s t} (h : Current s t) :
    ¬ Unborrowed s t.domain ∧ ¬ CanConsume s t.domain t.value := by
  have blocked : ¬ Unborrowed s t.domain := fun guard => guard t h rfl
  exact ⟨blocked,fun consume => blocked consume.2⟩

/-- Guard-fitting result only: no selected-core applicability claim or finalize step. -/
theorem active_blocks_guarded_core_permissions {s t core old new post}
    (h : Current s t) :
    ¬ RawDomainTransfer (Unborrowed s t.domain) core t.domain old new post ∧
    ¬ RawFinalizeDomain (Unborrowed s t.domain) core t.domain old post :=
  ⟨domain_transfer_rejects_missing_permission (active_blocks_original_consume h).1,
    finalize_domain_rejects_missing_permission (active_blocks_original_consume h).1⟩

theorem no_second_grant_in_single_loan_slice {c s d v m t post}
    (first : Begin c s d v m t post) (e w mode token again) :
    ¬ Begin c post e w mode token again := by
  intro second; rw [first.post_eq] at second
  have impossible := second.ready; simp [beginPost] at impossible

theorem exclusive_is_not_read_evidence {c s d v t post} :
    ¬ Begin c s d v .exclusiveRead t post := by
  intro h; cases h.readOnly

theorem closed_value_valid (s : State) (x : Value) (closed : F2.ScopeClosed (deps x)) : Valid s x := by
  induction x with
  | unit => trivial
  | stable t => exact False.elim (closed ⟨t.scope.index⟩ (by simp [deps,scopeTag]))
  | pair a b ha hb =>
    exact ⟨ha (fun q h => closed q (Finset.mem_union_left _ h)),
      hb (fun q h => closed q (Finset.mem_union_right _ h))⟩

theorem survivor_dependencies_included {xs x} (member : x ∈ xs) : deps x ⊆ survivorsDeps xs := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | tail
    · exact Finset.subset_union_left
    · exact (ih tail).trans Finset.subset_union_right

theorem end_wellFormed {c s} (wf : WellFormed c s) : WellFormed c (endPost s) := by
  refine ⟨wf.sourceWF,wf.history,?_,?_,?_⟩
  · simp [endPost]
  · intro t impossible; simp [endPost] at impossible
  · intro t impossible; simp [endPost] at impossible

theorem end_preserves_output_and_owner_obligations {c s t b post output}
    (event : End c s t b post output) :
    WellFormed c post ∧ post.source = s.source ∧ post.usedScopes = s.usedScopes ∧
    output = b ∧ exitDeps output = exitDeps b ∧
    Valid post output.result ∧ (∀ x ∈ output.survivors, Valid post x) ∧
    (∀ token, ¬ Current post token) := by
  rw [event.post_eq,event.output_eq]
  refine ⟨end_wellFormed event.before,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · apply closed_value_valid
    intro q member; exact event.scopeClosed q (Finset.mem_union_left _ member)
  · intro x member; apply closed_value_valid
    intro q dep
    exact event.scopeClosed q (Finset.mem_union_right _ (survivor_dependencies_included member dep))
  · intro token impossible; simp [Current,endPost] at impossible

theorem end_preserves_nonDiscardable_exit_obligations {c s t b post output owners domains}
    (event : End c s t b post output) :
    FreshDomainSource.NormalExit post.source owners domains ↔
    FreshDomainSource.NormalExit s.source owners domains := by
  rw [(end_preserves_output_and_owner_obligations event).2.1]

theorem double_close_rejected {c s t b post output} (first : End c s t b post output)
    (other out again) : ¬ End c post t other again out := by
  intro second
  exact (end_preserves_output_and_owner_obligations first).2.2.2.2.2.2.2 t second.current

theorem active_scope_must_close {s t} (current : Current s t) : s.active ≠ none := by
  intro empty; change s.active = some t at current; rw [empty] at current; cases current

theorem omitted_close_rejected {s t} (current : Current s t) : ¬ Complete s :=
  fun completed => active_scope_must_close current completed.2

theorem stable_result_and_nested_copy_escape_rejected (t : Token) :
    ¬ F2.ScopeClosed (deps (.stable t)) ∧
    ¬ F2.ScopeClosed (deps (.pair .unit (.pair (.stable t) (.stable t)))) := by
  constructor <;> intro closed <;> exact closed ⟨t.scope.index⟩ (by simp [deps,scopeTag])

theorem stored_survivor_escape_rejected {b : Boundary} {t : Token}
    (stored : scopeTag t.scope ∈ survivorsDeps b.survivors) :
    ¬ F2.ScopeClosed (exitDeps b) :=
  fun closed => closed ⟨t.scope.index⟩ (Finset.mem_union_right _ stored)

theorem ordinary_ref_copy_keeps_same_scope (t : Token) :
    deps (.pair (.stable t) (.stable t)) = deps (.stable t) := by simp [deps]

theorem wrong_domain_evidence_rejected {s t d} (wrong : t.domain ≠ d) : ¬ EvidenceFor s t d :=
  fun h => wrong h.2

/-- Coarse actual rich projection remains unchanged. It represents the original
D custody, NOT the new loan token. Nothing here upgrades F0 AcquireRef. -/
structure Refines (c : Context) (s : State) (g : Geometry) (birth slot rich : F1.Occupancy.State)
    (i : OneBackingIssuerSource.Interpretation) (typing : OneBackingSlotRich.Typing c)
    (handle : ClaimId) : Prop where
  loan : WellFormed c s
  original : RefinesDomain c s.source g birth slot rich i typing handle

theorem begin_refines {c s g birth slot rich i typing handle d v mode token post}
    (ref : Refines c s g birth slot rich i typing handle)
    (event : Begin c s d v mode token post) :
    Refines c post g birth slot rich i typing handle := by
  rw [event.post_eq]; exact ⟨begin_wellFormed ref.loan event.available,ref.original⟩

theorem end_refines {c s g birth slot rich i typing handle token b post output}
    (ref : Refines c s g birth slot rich i typing handle)
    (event : End c s token b post output) :
    Refines c post g birth slot rich i typing handle := by
  rw [event.post_eq]; exact ⟨end_wellFormed ref.loan,ref.original⟩

theorem current_has_actual_live_domain_and_carrier {c s g birth slot rich i typing handle t}
    (ref : Refines c s g birth slot rich i typing handle) (token : Current s t) :
    t.domain ∈ rich.flat.semantic.liveDomains ∧
    rich.flat.semantic.domainValueCarrier t.domain = some ⟨t.value⟩ := by
  have av := ref.loan.available t token
  have current := Finset.mem_union_left s.source.outgoing av
  refine ⟨?_,(ref.original.carriers t.domain t.value).mp current⟩
  rw [ref.original.domains]; exact Finset.mem_image.mpr ⟨(t.domain,t.value),current,rfl⟩

theorem still_no_selected_object_ref {c s g birth slot rich i typing handle}
    (ref : Refines c s g birth slot rich i typing handle) (stable access : Prop) (p : PtrToken) (d : DomainId) :
    ¬ AcquireRef stable access rich.flat.semantic p d :=
  domain_value_has_no_accepted_object_ref ref.original stable access p d

/-- The finite adapter retains DomainLive as well as the exact loan scope tag.
This connects the liveness component to actual F0, not just a ghost Domain name. -/
theorem current_token_dependencies {c s g birth slot rich i typing handle t}
    (ref : Refines c s g birth slot rich i typing handle) (token : Current s t) :
    scopeTag t.scope ∈ deps (.stable t) ∧
    F2.Dependency.externalFact (.domainLive t.domain) ∈ deps (.stable t) ∧
    Fact.domainLive t.domain ∈ LiveFacts rich.flat.semantic :=
  ⟨by simp [deps],by simp [deps],(current_has_actual_live_domain_and_carrier ref token).1⟩

def witnessHistory : ScopeHistory := ⟨1,{⟨0⟩},by
  intro q member; simp only [Finset.mem_singleton] at member; subst q; decide⟩
def witnessEntry := start FreshDomainWitness.after witnessHistory
def witnessToken := makeToken witnessEntry FreshDomainWitness.domain FreshDomainWitness.value
def witnessLoan := beginPost witnessEntry FreshDomainWitness.domain FreshDomainWitness.value
def witnessBoundary : Boundary := ⟨.unit,[],1⟩
def witnessClosed := endPost witnessLoan

theorem witness_entry_wellFormed : WellFormed OneBackingSlotWitness.context witnessEntry :=
  start_wellFormed FreshDomainWitness.complete_issue.2.1.source witnessHistory

theorem witness_available :
    (FreshDomainWitness.domain,FreshDomainWitness.value) ∈ witnessEntry.source.available := by
  change (FreshDomainWitness.domain,FreshDomainWitness.value) ∈ {(FreshDomainWitness.domain,FreshDomainWitness.value)}
  simp

theorem witness_acquisition :
    Begin OneBackingSlotWitness.context witnessEntry FreshDomainWitness.domain FreshDomainWitness.value
      .ordinaryRead witnessToken witnessLoan ∧ WellFormed OneBackingSlotWitness.context witnessLoan ∧
    Current witnessLoan witnessToken ∧ witnessToken.scope ∉ witnessEntry.usedScopes ∧
    witnessLoan.source = witnessEntry.source :=
  acquisition_constructed witness_entry_wellFormed rfl witness_available

theorem witness_end :
    End OneBackingSlotWitness.context witnessLoan witnessToken witnessBoundary witnessClosed witnessBoundary := by
  refine ⟨witness_acquisition.2.1,witness_acquisition.2.2.1,rfl,trivial,?_,?_,rfl,rfl⟩
  · intro x impossible; simp [witnessBoundary] at impossible
  · intro q impossible; simp [exitDeps,witnessBoundary,deps,survivorsDeps] at impossible

theorem witness_refinement :
    Refines OneBackingSlotWitness.context witnessLoan OneBackingIssuerWitness.afterGeometry
      OneBackingIssuerWitness.afterRich OneBackingSlotWitness.richSlot FreshDomainWitness.domainRich
      OneBackingIssuerWitness.afterInterpretation OneBackingSlotWitness.typing OneBackingSlotWitness.slotHandle ∧
    Refines OneBackingSlotWitness.context witnessClosed OneBackingIssuerWitness.afterGeometry
      OneBackingIssuerWitness.afterRich OneBackingSlotWitness.richSlot FreshDomainWitness.domainRich
      OneBackingIssuerWitness.afterInterpretation OneBackingSlotWitness.typing OneBackingSlotWitness.slotHandle := by
  have entry : Refines OneBackingSlotWitness.context witnessEntry OneBackingIssuerWitness.afterGeometry
      OneBackingIssuerWitness.afterRich OneBackingSlotWitness.richSlot FreshDomainWitness.domainRich
      OneBackingIssuerWitness.afterInterpretation OneBackingSlotWitness.typing OneBackingSlotWitness.slotHandle :=
    ⟨witness_entry_wellFormed,FreshDomainWitness.complete_issue.2.1⟩
  have loan := begin_refines entry witness_acquisition.1
  exact ⟨loan,end_refines loan witness_end⟩

/-- Nonempty old C plus original A/empty slot, all actual rich accounting intact.
Loan grant/discharge only change the adjunct scope registry. -/
theorem witness_round_trip_nonempty_frame :
    WellFormed OneBackingSlotWitness.context witnessClosed ∧ Complete witnessClosed ∧
    witnessClosed.source = witnessEntry.source ∧
    witnessClosed.source.owners.allocation = some 1004 ∧
    witnessClosed.source.owners.slot = some ⟨⟨1008,41,24⟩,.node⟩ ∧
    witnessClosed.source.available = {(FreshDomainWitness.domain,1009)} ∧
    F1.Occupancy.WellFormed OneBackingIssuerWitness.afterGeometry OneBackingSlotWitness.typing.layout FreshDomainWitness.domainRich ∧
    FreshDomainWitness.domainRich.ledger.active = {⟨10⟩,⟨0⟩} ∧
    (∀ l, FreshDomainWitness.domainRich.flat.semantic.occupancy l = .vacant) ∧
    FreshDomainWitness.domainRich.flat.semantic.usedIncarnations = ∅ :=
  ⟨(end_preserves_output_and_owner_obligations witness_end).1,⟨rfl,rfl⟩,rfl,rfl,rfl,rfl,
    FreshDomainWitness.complete_issue.2.2,
    FreshDomainWitness.owner_and_nonempty_rich_frame.2.2.2.2.2.2.1,
    FreshDomainWitness.no_typed_Node_before_initialize.1,
    FreshDomainWitness.no_typed_Node_before_initialize.2.1⟩

theorem witness_current_exact_identity :
    witnessToken = ⟨⟨1⟩,1009,⟨1⟩⟩ ∧
    EvidenceFor witnessLoan witnessToken FreshDomainWitness.domain ∧
    FreshDomainWitness.domainRich.flat.semantic.domainValueCarrier witnessToken.domain = some ⟨witnessToken.value⟩ :=
  ⟨rfl,⟨rfl,rfl⟩,(current_has_actual_live_domain_and_carrier witness_refinement.1 rfl).2⟩

theorem witness_copies_are_valid_within_scope :
    Valid witnessLoan (.pair (.stable witnessToken) (.stable witnessToken)) := ⟨rfl,rfl⟩

theorem witness_guard_is_not_a_rich_only_fact :
    CanConsume witnessEntry FreshDomainWitness.domain FreshDomainWitness.value ∧
    ¬ CanConsume witnessLoan FreshDomainWitness.domain FreshDomainWitness.value ∧
    witnessEntry.source = witnessLoan.source := by
  refine ⟨⟨witness_available,?_⟩,(active_blocks_original_consume (s := witnessLoan) (t := witnessToken) rfl).2,rfl⟩
  intro t impossible; simp [Current,witnessEntry,start] at impossible

theorem witness_retired_domain_rejected (mode t post) :
    ¬ Begin OneBackingSlotWitness.context witnessEntry ⟨0⟩ FreshDomainWitness.value mode t post := by
  intro event
  have absent : (⟨0⟩,FreshDomainWitness.value) ∉ witnessEntry.source.available := by
    change ((⟨0⟩ : DomainId),FreshDomainWitness.value) ∉ {(FreshDomainWitness.domain,FreshDomainWitness.value)}
    simp [FreshDomainWitness.domain,FreshDomainWitness.before,FreshDomainSource.newDomain,FreshDomainWitness.history,FreshDomainSource.start]
  exact absent event.available

theorem witness_wrong_current_value_rejected (mode t post) :
    ¬ Begin OneBackingSlotWitness.context witnessEntry FreshDomainWitness.domain 1010 mode t post := by
  intro event
  have absent : (FreshDomainWitness.domain,1010) ∉ witnessEntry.source.available := by
    change (FreshDomainWitness.domain,1010) ∉ {(FreshDomainWitness.domain,1009)}
    simp
  exact absent event.available

theorem witness_pregrant_and_retired_scope_tokens_rejected :
    ¬ Current witnessEntry witnessToken ∧
    ¬ Current witnessLoan {witnessToken with scope := ⟨0⟩} ∧
    ¬ Current witnessClosed witnessToken := by
  constructor
  · simp [Current,witnessEntry,start]
  · constructor
    · change ¬ some (⟨⟨1⟩,1009,⟨1⟩⟩ : Token) = some ⟨⟨1⟩,1009,⟨0⟩⟩
      decide
    · simp [Current,witnessClosed,endPost]

def witnessMoved : State := {witnessLoan with
  source := FreshDomainSource.forwardPost witnessLoan.source witnessToken.domain witnessToken.value}

theorem witness_moved_domain_under_active_loan_rejected :
    FreshDomainSource.SourceWF OneBackingSlotWitness.context witnessMoved.source ∧
    ¬ WellFormed OneBackingSlotWitness.context witnessMoved := by
  refine ⟨FreshDomainSource.forward_wellFormed witness_acquisition.2.1.sourceWF witness_available,?_⟩
  intro wf
  have available := wf.available witnessToken rfl
  change (witnessToken.domain,witnessToken.value) ∈ (FreshDomainSource.forwardPost witnessLoan.source witnessToken.domain witnessToken.value).available at available
  simp [FreshDomainSource.forwardPost] at available

def witnessMissingA : State := {witnessLoan with
  source := {witnessLoan.source with owners := {witnessLoan.source.owners with allocation := none}}}

theorem witness_missing_A_rejected : ¬ WellFormed OneBackingSlotWitness.context witnessMissingA := by
  intro wf
  have wfOwners := wf.sourceWF.owners
  have a := wfOwners.allocation
  rw [wf.sourceWF.slot] at a
  simp [witnessMissingA,expectedAllocation] at a

def witnessMissingSlot : State := {witnessLoan with
  source := {witnessLoan.source with owners := {witnessLoan.source.owners with slot := none}}}

theorem witness_missing_slot_rejected : ¬ WellFormed OneBackingSlotWitness.context witnessMissingSlot := by
  intro wf
  have slot := wf.sourceWF.owners.slot
  rw [wf.sourceWF.slot] at slot
  simp [witnessMissingSlot,expectedSlot] at slot

def witnessDuplicatedD : State := {witnessLoan with source := {witnessLoan.source with
  available := insert (FreshDomainWitness.domain,1010) witnessLoan.source.available}}

theorem witness_duplicated_D_rejected : ¬ WellFormed OneBackingSlotWitness.context witnessDuplicatedD := by
  intro wf
  have original : (FreshDomainWitness.domain,1009) ∈ FreshDomainSource.current witnessDuplicatedD.source := by
    change (FreshDomainWitness.domain,1009) ∈ insert (FreshDomainWitness.domain,1010) {(FreshDomainWitness.domain,1009)} ∪ ∅
    simp
  have duplicate : (FreshDomainWitness.domain,1010) ∈ FreshDomainSource.current witnessDuplicatedD.source := by
    simp [FreshDomainSource.current,witnessDuplicatedD]
  have impossible := wf.sourceWF.domainUnique _ _ _ original duplicate
  omega

theorem witness_result_survivor_and_once_checks :
    ¬ F2.ScopeClosed (exitDeps ⟨.stable witnessToken,[],1⟩) ∧
    ¬ F2.ScopeClosed (exitDeps ⟨.unit,[.pair .unit (.stable witnessToken)],1⟩) ∧
    (∀ b post output, b.evaluations ≠ 1 →
      ¬ End OneBackingSlotWitness.context witnessLoan witnessToken b post output) := by
  refine ⟨?_,?_,?_⟩
  · intro closed; exact closed ⟨witnessToken.scope.index⟩ (by simp [exitDeps,deps,scopeTag])
  · intro closed; exact closed ⟨witnessToken.scope.index⟩ (by simp [exitDeps,deps,scopeTag,survivorsDeps])
  · intro b post output notOnce event; exact notOnce event.once

theorem witness_selected_core_bridge_still_missing (stable access : Prop) (p : PtrToken) :
    Current witnessLoan witnessToken ∧
    ¬ AcquireRef stable access FreshDomainWitness.domainRich.flat.semantic p FreshDomainWitness.domain :=
  ⟨rfl,still_no_selected_object_ref witness_refinement.1 stable access p _⟩

theorem witness_after_close_original_responsibility_available :
    CanConsume witnessClosed FreshDomainWitness.domain FreshDomainWitness.value ∧
    witnessToken.scope ∈ witnessClosed.usedScopes ∧
    ¬ FreshDomainSource.NormalExit witnessClosed.source witnessClosed.source.owners ∅ := by
  refine ⟨⟨witness_available,?_⟩,by decide,?_⟩
  · intro t impossible; simp [Current,witnessClosed,endPost] at impossible
  · intro exit
    have impossible := exit.domains
    change (∅ : Finset (DomainId × Nat)) = {(FreshDomainWitness.domain,FreshDomainWitness.value)} at impossible
    have : (FreshDomainWitness.domain,FreshDomainWitness.value) ∈ (∅ : Finset (DomainId × Nat)) := by
      rw [impossible]; simp
    exact Finset.notMem_empty _ this

end
end NewLang.Adjunct.DomainValueReadLoan
