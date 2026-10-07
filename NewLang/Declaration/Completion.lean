import NewLang.F0.Reference
import Mathlib.Data.Finset.Basic

/-! Bounded declaration/type-graph model for Draft 17.21 §16.3.
No runtime layout, parser, object construction, or recursive value semantics. -/
namespace NewLang.Declaration

structure NominalId where
  index : Nat
  deriving DecidableEq

structure FieldId where
  index : Nat
  deriving DecidableEq

/-- Finite type expressions for the selected profile and its negative controls.
Option is an ordinary payload constructor, not an optional-pointer special case. -/
inductive Ty where
  | byte
  | nominal (id : NominalId)
  | ptr (target : NominalId)
  | option (payload : Ty)
  | unresolved
  deriving DecidableEq

structure Field where
  identity : FieldId
  type : Ty
  deriving DecidableEq

/-- Exactly two declaration-order fields in this bounded task. -/
structure Fields where
  link : Field
  payload : Field
  deriving DecidableEq

inductive Phase where
  | incomplete
  | complete (fields : Fields)
  deriving DecidableEq

/-- Header identity and field labels are supplied after name admission; they are
not allocated from physical source position by this model. -/
structure Header where
  identity : NominalId
  linkLabel : FieldId
  payloadLabel : FieldId
  phase : Phase
  deriving DecidableEq

structure Request where
  identity : NominalId
  fields : Fields
  deriving DecidableEq

/-- Candidate graph sees proposed fields before public completion. -/
inductive ValueEdge (h : NominalId) (fields : Fields) : Ty → Ty → Prop
  | link : ValueEdge h fields (.nominal h) fields.link.type
  | payload : ValueEdge h fields (.nominal h) fields.payload.type
  | option (t : Ty) : ValueEdge h fields (.option t) t

inductive TargetEdge : Ty → Ty → Prop
  | ptr (h : NominalId) : TargetEdge (.ptr h) (.nominal h)

def NoValueCycle (h : NominalId) (fields : Fields) : Prop :=
  ¬ Relation.TransGen (ValueEdge h fields) (.nominal h) (.nominal h)

def ExactTypes (h : NominalId) (fields : Fields) : Prop :=
  fields.link.type = .option (.ptr h) ∧ fields.payload.type = .byte

def Eligible (s : Header) (r : Request) : Prop :=
  s.phase = .incomplete ∧ r.identity = s.identity ∧
  s.linkLabel ≠ s.payloadLabel ∧ r.fields.link.identity = s.linkLabel ∧
  r.fields.payload.identity = s.payloadLabel ∧ ExactTypes s.identity r.fields ∧
  NoValueCycle s.identity r.fields

def completeCandidate (s : Header) (fields : Fields) : Header :=
  { s with phase := .complete fields }

def CompleteStep (s : Header) (r : Request) (post : Header) : Prop :=
  Eligible s r ∧ post = completeCandidate s r.fields

noncomputable def complete? (s : Header) (r : Request) : Option Header := by
  classical
  exact if Eligible s r then some (completeCandidate s r.fields) else none

/-- The two permitted capabilities use ordinary structural composition. The depth
index exhibits a finite derivation; ptr has no target-property premise. -/
inductive Capability where
  | copy
  | discardable
  deriving DecidableEq

def committedFields (s : Header) (h : NominalId) : Option Fields :=
  if h = s.identity then match s.phase with
    | .incomplete => none
    | .complete fields => some fields
  else none

inductive Derives (s : Header) (cap : Capability) : Nat → Ty → Prop
  | byte : Derives s cap 0 .byte
  | ptr (h : NominalId) : Derives s cap 0 (.ptr h)
  | option {n t} : Derives s cap n t → Derives s cap (n+1) (.option t)
  | nominal {h fields n m} : (∃ initial request, CompleteStep initial request s) →
      committedFields s h = some fields →
      Derives s cap n fields.link.type → Derives s cap m fields.payload.type →
      Derives s cap (max n m + 1) (.nominal h)

def HasProperty (s : Header) (cap : Capability) (t : Ty) : Prop :=
  ∃ depth, Derives s cap depth t

/-- Type formation is a pure operation; supplied runtime state is a frame. -/
structure World where
  header : Header
  runtime : F0.State

def PtrFormation (pre : World) (target : NominalId) (type : Ty) (post : World) : Prop :=
  target = pre.header.identity ∧ type = .ptr target ∧ post = pre

def CompletionInWorld (pre : World) (r : Request) (post : World) : Prop :=
  CompleteStep pre.header r post.header ∧ post.runtime = pre.runtime

/-- Private staging can fail after a prior staged completion. Nothing is published
by this function. In particular a second completion fails the whole attempt. -/
noncomputable def stage : Header → List Request → Option Header
  | s, [] => some s
  | s, r :: rs => match complete? s r with
      | none => none
      | some next => stage next rs

/-- Public values have a complete field set, never an incomplete header. -/
structure Published where
  identity : NominalId
  linkLabel : FieldId
  payloadLabel : FieldId
  fields : Fields
  deriving DecidableEq

def asPublished (s : Header) : Option Published := match s.phase with
  | .incomplete => none
  | .complete fields => some ⟨s.identity,s.linkLabel,s.payloadLabel,fields⟩

/-- Abstract atomic publication boundary. The snapshot is opaque prior public
context, not a production registry or a proof of an implementation's rollback. -/
inductive Outcome where
  | rejected
  | accepted (declaration : Published)
  deriving DecidableEq

noncomputable def registrationResult (s : Header) (requests : List Request) : Outcome :=
  if s.phase = .incomplete then
    match stage s requests with
    | none => .rejected
    | some final => match asPublished final with
        | none => .rejected
        | some published => .accepted published
  else .rejected

noncomputable def publish (snapshot : Option Published) (s : Header) (requests : List Request) :
    Option Published × Outcome :=
  let outcome := registrationResult s requests
  match outcome with
  | .rejected => (snapshot, .rejected)
  | .accepted declaration => (some declaration, outcome)

/-- Closed-category collection: other declaration/body positions are opaque.
Plans already carry semantic IDs; this does not implement a name allocator. -/
structure Plan where
  header : Header
  request : Request
  deriving DecidableEq

inductive Event where
  | declaration (plan : Plan)
  | other (tag : Nat)
  deriving DecidableEq

def headerSet (events : List Event) : Finset Plan :=
  (events.filterMap fun event => match event with
    | .declaration plan => some plan
    | .other _ => none).toFinset

def headerCount : List Event → Nat
  | [] => 0
  | .declaration _ :: rest => 1 + headerCount rest
  | .other _ :: rest => headerCount rest

/-- Count occurrences, not only distinct identities: duplicates are not erased. -/
def BoundedCollection (events : List Event) : Prop := headerCount events ≤ 1

end NewLang.Declaration
