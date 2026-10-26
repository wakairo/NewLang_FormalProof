import NewLang.F1.WellFormed

/-!
F72: a bounded typed lexical evaluator, before either IF arm.
This adjunct has no parser, compiler registry, Domain issuer, or rich-state lift.
Creation tags are local to one evaluation from empty history.
-/

namespace NewLang.Adjunct.LexicalPrefix

inductive Two where
  | first
  | second
  deriving DecidableEq, Repr

inductive Path where
  | whole
  | field (index : Two)
  deriving DecidableEq, Repr

abbrev RootId := Nat × Two
abbrev NodeId := RootId × Path

structure Incarnation where
  creation : NodeId
  deriving DecidableEq

structure CurrentFact where
  creation : NodeId
  deriving DecidableEq

structure Nominal where
  name : String
  fieldName : Two → String
  distinctFields : fieldName .first ≠ fieldName .second

/-- The permutation maps initializer source positions to declaration indices. -/
structure Initializer where
  order : Equiv.Perm Two
  literal : Two → Fin 256

def declaredValue (i : Initializer) (field : Two) : Fin 256 :=
  i.literal (i.order.symm field)

structure TargetConfig where
  usizeWidth : Nat
  positiveWidth : 0 < usizeWidth

structure UsizeLiteral (target : TargetConfig) where
  value : Nat
  inRange : value < 2 ^ target.usizeWidth

inductive Comparison where
  | equal
  | less
  deriving DecidableEq

/-- Formation includes complete literal initializers, names and target typing;
it includes no saved entry state, lifetime support, or authority witness. -/
structure Prefix where
  blockInstance : Nat
  nominal : Nominal
  bindingName : Two → String
  distinctBindings : bindingName .first ≠ bindingName .second
  init : Two → Initializer
  target : TargetConfig
  lhs : UsizeLiteral target
  rhs : UsizeLiteral target
  comparison : Comparison

def rootId (p : Prefix) (b : Two) : RootId := (p.blockInstance, b)

def condition (p : Prefix) : Bool :=
  match p.comparison with
  | .equal => decide (p.lhs.value = p.rhs.value)
  | .less => decide (p.lhs.value < p.rhs.value)

def conditionProposition (p : Prefix) : Prop :=
  match p.comparison with
  | .equal => p.lhs.value = p.rhs.value
  | .less => p.lhs.value < p.rhs.value

inductive Carrier where
  | aggregate (root : RootId)
  | member (root : RootId) (field : Two)
  deriving DecidableEq

structure InstalledAggregate where
  original : RootId
  bindingName : String
  nominalName : String
  fieldName : Two → String
  payload : Two → Fin 256

structure NodeRecord where
  identity : NodeId
  incarnation : Incarnation
  currentFact : CurrentFact
  carrier : Carrier
  scalar : Option (Fin 256)
  dependencies : List NodeId

def aggregate (p : Prefix) (b : Two) : InstalledAggregate :=
  ⟨rootId p b, p.bindingName b, p.nominal.name, p.nominal.fieldName,
    declaredValue (p.init b)⟩

/-- Creation happens only when the complete aggregate is installed.
Members carry their original aggregate owner, never a standalone root. -/
def record (p : Prefix) (b : Two) : Path → NodeRecord
  | .whole =>
    ⟨(rootId p b, .whole), ⟨(rootId p b, .whole)⟩,
      ⟨(rootId p b, .whole)⟩, .aggregate (rootId p b), none, []⟩
  | .field f =>
    ⟨(rootId p b, .field f), ⟨(rootId p b, .field f)⟩,
      ⟨(rootId p b, .field f)⟩, .member (rootId p b) f,
      some (declaredValue (p.init b) f), []⟩

def records (p : Prefix) (b : Two) : List NodeRecord :=
  [record p b .whole, record p b (.field .first), record p b (.field .second)]

inductive Temporary where
  | lhs
  | rhs
  | boolean
  deriving DecidableEq

inductive Event where
  | enter (block : Nat)
  | literal (owner : RootId) (sourcePosition field : Two) (value : Fin 256)
  | bind (owner : RootId)
  | usize (temporary : Temporary) (value width : Nat)
  | compare (value : Bool)
  | endTemporaries
  | commonCut
  deriving DecidableEq

structure State where
  activeBlocks : List Nat
  history : List Event
  installed : List InstalledAggregate
  nodes : List NodeRecord
  activeTemporaries : List Temporary
  endedTemporaries : List Temporary
  knownCondition : Option Bool
  commonCut : Bool

def empty : State := ⟨[], [], [], [], [], [], none, false⟩

def enterBlock (p : Prefix) (s : State) : State :=
  { s with activeBlocks := s.activeBlocks ++ [p.blockInstance]
           history := s.history ++ [.enter p.blockInstance] }

def bindingEvents (p : Prefix) (b : Two) : List Event :=
  [.literal (rootId p b) .first ((p.init b).order .first) ((p.init b).literal .first),
   .literal (rootId p b) .second ((p.init b).order .second) ((p.init b).literal .second),
   .bind (rootId p b)]

def bindAggregate (p : Prefix) (b : Two) (s : State) : State :=
  { s with history := s.history ++ bindingEvents p b
           installed := s.installed ++ [aggregate p b]
           nodes := s.nodes ++ records p b }

def compareEvents (p : Prefix) : List Event :=
  [.usize .lhs p.lhs.value p.target.usizeWidth,
   .usize .rhs p.rhs.value p.target.usizeWidth, .compare (condition p)]

def compareLiterals (p : Prefix) (s : State) : State :=
  { s with history := s.history ++ compareEvents p
           activeTemporaries := [.lhs, .rhs, .boolean]
           knownCondition := some (condition p) }

def endComparison (s : State) : State :=
  { s with history := s.history ++ [.endTemporaries, .commonCut]
           endedTemporaries := s.endedTemporaries ++ s.activeTemporaries
           activeTemporaries := []
           commonCut := true }

/-- This is the complete supported program, in source execution order.
There are no arms, loans, calls, or changes in this AST. -/
def evaluate (p : Prefix) : State :=
  endComparison (compareLiterals p
    (bindAggregate p .second (bindAggregate p .first (enterBlock p empty))))

def originalRoots (s : State) : List NodeId :=
  s.installed.map (fun a => (a.original, .whole))

def nodeIds (s : State) : List NodeId := s.nodes.map NodeRecord.identity

/-- Historical entry alone is insufficient: the block must still be active
and the original aggregate must still be installed. This is lexical support
only; no stability/access token or explicit nonCopy value is represented. -/
def LexicallySupported (s : State) (r : RootId) : Prop :=
  r.1 ∈ s.activeBlocks ∧ Event.enter r.1 ∈ s.history ∧
  Event.bind r ∈ s.history ∧ r ∈ s.installed.map InstalledAggregate.original

theorem evaluated_installed (p : Prefix) :
    (evaluate p).installed = [aggregate p .first, aggregate p .second] := rfl

theorem evaluated_nodes (p : Prefix) :
    (evaluate p).nodes = records p .first ++ records p .second := rfl

theorem evaluated_blocks (p : Prefix) :
    (evaluate p).activeBlocks = [p.blockInstance] := rfl

theorem evaluated_history (p : Prefix) :
    (evaluate p).history = [.enter p.blockInstance] ++
      bindingEvents p .first ++ bindingEvents p .second ++
      compareEvents p ++ [.endTemporaries, .commonCut] := rfl

theorem roots_exact (p : Prefix) :
    originalRoots (evaluate p) =
      [(rootId p .first, .whole), (rootId p .second, .whole)] := rfl

theorem nodes_exact (p : Prefix) :
    nodeIds (evaluate p) =
      [(rootId p .first, .whole), (rootId p .first, .field .first),
       (rootId p .first, .field .second), (rootId p .second, .whole),
       (rootId p .second, .field .first), (rootId p .second, .field .second)] := rfl

theorem node_creation_fresh (p : Prefix) : (nodeIds (evaluate p)).Nodup := by
  rw [nodes_exact]
  simp [rootId]

theorem incarnation_creation_fresh (p : Prefix) :
    ((evaluate p).nodes.map NodeRecord.incarnation).Nodup := by
  rw [evaluated_nodes]
  simp [records, record, rootId]

theorem current_fact_creation_fresh (p : Prefix) :
    ((evaluate p).nodes.map NodeRecord.currentFact).Nodup := by
  rw [evaluated_nodes]
  simp [records, record, rootId]

theorem binding_sites_distinct (p : Prefix) :
    rootId p .first ≠ rootId p .second := by
  simp [rootId]

theorem root_and_node_counts (p : Prefix) :
    (originalRoots (evaluate p)).length = 2 ∧ (evaluate p).nodes.length = 6 := by
  constructor <;> rfl

theorem child_not_original_root (p : Prefix) (b f : Two) :
    (rootId p b, Path.field f) ∉ originalRoots (evaluate p) := by
  rw [roots_exact]
  simp

theorem lexical_support_derived (p : Prefix) (b : Two) :
    LexicallySupported (evaluate p) (rootId p b) := by
  cases b <;>
    simp [LexicallySupported, evaluated_blocks, evaluated_history,
      evaluated_installed, bindingEvents, aggregate, rootId]

theorem initializer_source_order (p : Prefix) (b position : Two) :
    (record p b (.field ((p.init b).order position))).scalar =
      some ((p.init b).literal position) := by
  simp [record, declaredValue]

theorem member_owned_by_original (p : Prefix) (b f : Two) :
    (record p b (.field f)).carrier = .member (rootId p b) f := rfl

theorem whole_owned_by_original (p : Prefix) (b : Two) :
    (record p b .whole).carrier = .aggregate (rootId p b) := rfl

theorem literal_dependencies_empty (p : Prefix) (b : Two) (path : Path) :
    (record p b path).dependencies = [] := by
  cases path <;> rfl

theorem record_identity (p : Prefix) (b : Two) (path : Path) :
    (record p b path).identity = (rootId p b, path) := by
  cases path <;> rfl

theorem record_incarnation (p : Prefix) (b : Two) (path : Path) :
    (record p b path).incarnation = ⟨(rootId p b, path)⟩ := by
  cases path <;> rfl

theorem record_current_fact (p : Prefix) (b : Two) (path : Path) :
    (record p b path).currentFact = ⟨(rootId p b, path)⟩ := by
  cases path <;> rfl

theorem incarnation_distinguishes_nodes (p : Prefix) (b c : Two) (x y : Path)
    (h : (record p b x).incarnation = (record p c y).incarnation) :
    (rootId p b, x) = (rootId p c, y) := by
  rw [record_incarnation, record_incarnation] at h
  exact congrArg Incarnation.creation h

theorem current_fact_distinguishes_nodes (p : Prefix) (b c : Two) (x y : Path)
    (h : (record p b x).currentFact = (record p c y).currentFact) :
    (rootId p b, x) = (rootId p c, y) := by
  rw [record_current_fact, record_current_fact] at h
  exact congrArg CurrentFact.creation h

theorem condition_true_iff (p : Prefix) :
    condition p = true ↔ conditionProposition p := by
  cases h : p.comparison <;> simp [condition, conditionProposition, h]

theorem condition_false_iff (p : Prefix) :
    condition p = false ↔ ¬ conditionProposition p := by
  cases h : p.comparison <;> simp [condition, conditionProposition, h]

theorem target_range (p : Prefix) :
    0 < p.target.usizeWidth ∧
    p.lhs.value < 2 ^ p.target.usizeWidth ∧
    p.rhs.value < 2 ^ p.target.usizeWidth :=
  ⟨p.target.positiveWidth, p.lhs.inRange, p.rhs.inRange⟩

theorem comparison_ended_at_common_cut (p : Prefix) :
    (evaluate p).knownCondition = some (condition p) ∧
    (evaluate p).activeTemporaries = [] ∧
    (evaluate p).endedTemporaries = [.lhs, .rhs, .boolean] ∧
    (evaluate p).commonCut = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All conclusions are derived from one typed AST, never a host entry or POST. -/
theorem typed_prefix_evaluation (p : Prefix) :
    (originalRoots (evaluate p)).length = 2 ∧
    (evaluate p).nodes.length = 6 ∧
    (nodeIds (evaluate p)).Nodup ∧
    (∀ b, LexicallySupported (evaluate p) (rootId p b)) ∧
    (∀ b f, (rootId p b, Path.field f) ∉ originalRoots (evaluate p)) ∧
    (∀ b position, (record p b (.field ((p.init b).order position))).scalar =
      some ((p.init b).literal position)) ∧
    (∀ b path, (record p b path).dependencies = []) ∧
    (evaluate p).knownCondition = some (condition p) ∧
    (evaluate p).activeTemporaries = [] ∧
    (evaluate p).endedTemporaries = [.lhs, .rhs, .boolean] ∧
    (evaluate p).commonCut = true := by
  exact ⟨(root_and_node_counts p).1, (root_and_node_counts p).2,
    node_creation_fresh p, lexical_support_derived p, child_not_original_root p,
    initializer_source_order p, literal_dependencies_empty p,
    comparison_ended_at_common_cut p⟩

/-- A proposed *limited* observable encoding. Its injectivity must be supplied
and checked at a later implementation boundary; nothing constructs C evidence. -/
structure Encoding where
  node : NodeId → Nat
  nodeInjective : Function.Injective node
  incarnation : Incarnation → Nat
  incarnationInjective : Function.Injective incarnation
  fact : CurrentFact → Nat
  factInjective : Function.Injective fact

structure ObservableNode where
  identity : Nat
  incarnation : Nat
  currentFact : Nat
  owner : Nat
  scalar : Option (Fin 256)
  dependencies : List Nat

structure ObservableEntry where
  roots : List Nat
  nodes : List ObservableNode
  activeBlocks : List Nat
  condition : Option Bool
  temporaries : List Temporary
  commonCut : Bool

def observeNode (e : Encoding) (n : NodeRecord) : ObservableNode :=
  ⟨e.node n.identity, e.incarnation n.incarnation, e.fact n.currentFact,
    e.node (n.identity.1, .whole), n.scalar, n.dependencies.map e.node⟩

def observe (e : Encoding) (s : State) : ObservableEntry :=
  ⟨(originalRoots s).map e.node, s.nodes.map (observeNode e), s.activeBlocks,
    s.knownCondition, s.activeTemporaries, s.commonCut⟩

/-- Definition only: no theorem connects a compiler snapshot to this relation.
This observes values/ownership, not F1 authority or parser/plan authenticity. -/
def Represents (p : Prefix) (c : ObservableEntry) : Prop :=
  ∃ e : Encoding, c = observe e (evaluate p)

/-- Accepted F1 rejects the naive authority-free direct lift. -/
theorem live_roots_empty_domains_not_wellFormed (s : NewLang.F1.State)
    (nonempty : s.liveRoots.Nonempty) (emptyDomains : s.liveDomains = ∅) :
    ¬ NewLang.F1.WellFormed s := by
  intro wf
  rcases nonempty with ⟨root, live⟩
  have domainLive := wf.domainsValid root live
  rw [emptyDomains] at domainLive
  simpa using domainLive

#print axioms typed_prefix_evaluation
#print axioms incarnation_creation_fresh
#print axioms current_fact_creation_fresh
#print axioms incarnation_distinguishes_nodes
#print axioms current_fact_distinguishes_nodes
#print axioms condition_true_iff
#print axioms condition_false_iff
#print axioms target_range
#print axioms member_owned_by_original
#print axioms whole_owned_by_original
#print axioms live_roots_empty_domains_not_wellFormed

end NewLang.Adjunct.LexicalPrefix
