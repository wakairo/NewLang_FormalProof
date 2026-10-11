import NewLang.Adjunct.OneBackingSlotWitness

/-! Issue #57. A selected atomic lifetime_domain() source-spec adjunct.
Domain names/history and nonCopy authority are explicit. No lexical loan
operation is invented: the accepted Domain-value loan bridge is audited
separately. None never enters this successful-slot successor. -/
namespace NewLang.Adjunct.FreshDomainSource
open F0 OneBackingSlotSource
noncomputable section

inductive Phase | ready | issued | forwarded deriving DecidableEq
inductive Extra | typedRoot | pointer | incarnation | scopedRef deriving DecidableEq

/-- Retired domain history is independent of backing identities/addresses.
No currently available D is supplied here. Values share a source-name space
with the owner graph; the next new value is derived beyond that graph. -/
structure History (c : Context) where
  nextDomain : Nat
  usedDomains : Finset DomainId
  retiredValues : Finset Nat
  domainBelow : ∀ d ∈ usedDomains, d.index < nextDomain
  valueBelow : ∀ v ∈ retiredValues, v < c.packet.base+5

structure State where
  owners : Custody
  phase : Phase
  nextDomain : Nat
  usedDomains : Finset DomainId
  nextValue : Nat
  usedValues : Finset Nat
  available : Finset (DomainId × Nat)
  outgoing : Finset (DomainId × Nat)
  consumed : Finset Nat
  extras : Finset Extra

def current (s : State) : Finset (DomainId × Nat) := s.available ∪ s.outgoing
def newDomain (s : State) : DomainId := ⟨s.nextDomain⟩
def newValue (s : State) : Nat := s.nextValue

/-- A domain has one original nonCopy value in one current place: local OR
normal result. The union alone would hide a duplicated placement, hence the
independent disjointness obligation. -/
structure SourceWF (c : Context) (s : State) : Prop where
  owners : OneBackingSlotSource.SourceWF c s.owners
  slot : s.owners.phase = OneBackingSlotSource.Phase.slot
  domainHistory : ∀ d ∈ s.usedDomains, d.index < s.nextDomain
  valueHistory : ∀ v ∈ s.usedValues, v < s.nextValue
  ownerBelow : ∀ v b, (v,b) ∈ s.owners.current → v < s.nextValue
  recorded : ∀ d v, (d,v) ∈ current s → d ∈ s.usedDomains ∧ v ∈ s.usedValues
  domainUnique : ∀ d v w, (d,v) ∈ current s → (d,w) ∈ current s → v = w
  valueUnique : ∀ d e v, (d,v) ∈ current s → (e,v) ∈ current s → d = e
  distinctPlaces : Disjoint s.available s.outgoing
  separateOwners : ∀ d v, (d,v) ∈ current s → ∀ b, (v,b) ∉ s.owners.current
  consumedUnavailable : ∀ d v, (d,v) ∈ s.available → v ∉ s.consumed
  consumedRecorded : s.consumed ⊆ s.usedValues
  noEarly : s.extras = ∅

def start (c : Context) (owners : Custody) (h : History c) : State :=
  ⟨owners,.ready,h.nextDomain,h.usedDomains,c.packet.base+5,h.retiredValues,∅,∅,∅,∅⟩

/-- No post grant, live D, current carrier, or matched Domain is a PRE input. -/
def issuePost (s : State) : State :=
  {s with
    phase := .issued
    nextDomain := s.nextDomain+1
    usedDomains := insert (newDomain s) s.usedDomains
    nextValue := s.nextValue+1
    usedValues := insert (newValue s) s.usedValues
    available := insert (newDomain s,newValue s) s.available}

/-- The ONE selected call in this slice. Another distinct fresh call is outside
this task; it is not declared language-invalid. No fallible Domain API added. -/
structure Issue (c : Context) (s post : State) : Prop where
  before : SourceWF c s
  phase : s.phase = .ready
  noDomain : current s = ∅
  post_eq : post = issuePost s

/-- Minimal ordinary affine value forwarding, not Domain finalization. The
same identity/value leaves its local placement and appears in a result. -/
def forwardPost (s : State) (d : DomainId) (v : Nat) : State :=
  {s with
    phase := .forwarded
    available := s.available.erase (d,v)
    outgoing := insert (d,v) s.outgoing
    consumed := insert v s.consumed}

structure Forward (c : Context) (s : State) (d : DomainId) (v : Nat) (post : State) : Prop where
  before : SourceWF c s
  available : (d,v) ∈ s.available
  post_eq : post = forwardPost s d v

/-- All nonDiscardable responsibility must be forwarded on normal completion.
This is a custody obligation, not terminal release of A/slot/D. -/
structure NormalExit (s : State) (ownersResult : Custody) (domainsResult : Finset (DomainId × Nat)) : Prop where
  owners : ownersResult = s.owners
  domains : domainsResult = current s

theorem slot_owner_values_below {c owners}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : OneBackingSlotSource.SourceWF c owners) (slot : owners.phase = .slot) :
    ∀ v b, (v,b) ∈ owners.current → v < c.packet.base+5 := by
  intro v b edge
  rw [wf.currentExact,slot] at edge
  rcases Finset.mem_union.mp edge with packet | old
  · simp [packetGraph] at packet
    rcases packet with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  · have := frame_value_below oldWF old; omega

theorem start_wellFormed {c owners}
    (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : OneBackingSlotSource.SourceWF c owners) (slot : owners.phase = .slot) (h : History c) :
    SourceWF c (start c owners h) := by
  refine ⟨wf,slot,h.domainBelow,h.valueBelow,slot_owner_values_below oldWF wf slot,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  all_goals simp [current,start]

theorem domain_and_value_fresh {c s} (wf : SourceWF c s) :
    newDomain s ∉ s.usedDomains ∧ newValue s ∉ s.usedValues ∧
    ∀ b, (newValue s,b) ∉ s.owners.current := by
  refine ⟨?_,?_,?_⟩
  · intro member; have := wf.domainHistory _ member; simp [newDomain] at this
  · intro member; have := wf.valueHistory _ member; simp [newValue] at this
  · intro b edge; have := wf.ownerBelow _ _ edge; simp [newValue] at this

theorem no_domain_implies_places_empty {s} (empty : current s = ∅) :
    s.available = ∅ ∧ s.outgoing = ∅ := by
  exact Finset.union_eq_empty.mp empty

theorem issue_wellFormed {c s} (wf : SourceWF c s) (empty : current s = ∅) :
    SourceWF c (issuePost s) := by
  have av := (no_domain_implies_places_empty empty).1
  have out := (no_domain_implies_places_empty empty).2
  have fresh := domain_and_value_fresh wf
  constructor
  · exact wf.owners
  · exact wf.slot
  · intro d member
    simp only [issuePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [issuePost,newDomain]
    · have := wf.domainHistory d member; change d.index < s.nextDomain+1; omega
  · intro v member
    simp only [issuePost,Finset.mem_insert] at member
    rcases member with rfl | member
    · simp [issuePost,newValue]
    · have := wf.valueHistory v member; change v < s.nextValue+1; omega
  · intro v b edge; have := wf.ownerBelow v b edge; change v < s.nextValue+1; omega
  · intro d v member
    simp [current,issuePost,av,out] at member
    rcases member with ⟨rfl,rfl⟩; simp [issuePost]
  · intro d v w a b
    simp [current,issuePost,av,out] at a b
    exact a.2.trans b.2.symm
  · intro d e v a b
    simp [current,issuePost,av,out] at a b
    exact a.1.trans b.1.symm
  · simp [issuePost,out]
  · intro d v member
    simp [current,issuePost,av,out] at member
    rcases member with ⟨rfl,rfl⟩; exact fresh.2.2
  · intro d v member
    simp [issuePost,av] at member
    rcases member with ⟨rfl,rfl⟩
    exact fun member => fresh.2.1 (wf.consumedRecorded member)
  · exact wf.consumedRecorded.trans (Finset.subset_insert _ _)
  · exact wf.noEarly

/-- Forwarding changes current placement, not the original D/value inventory. -/
theorem forward_current {s d v} (member : (d,v) ∈ s.available) :
    current (forwardPost s d v) = current s := by
  ext entry
  by_cases eq : entry = (d,v)
  · subst entry; simp [current,forwardPost,member]
  · simp [current,forwardPost,eq]

theorem forward_wellFormed {c s d v} (wf : SourceWF c s)
    (member : (d,v) ∈ s.available) : SourceWF c (forwardPost s d v) := by
  have same := forward_current member
  have cur : (d,v) ∈ current s := Finset.mem_union_left _ member
  have history := wf.recorded d v cur
  constructor
  · exact wf.owners
  · exact wf.slot
  · exact wf.domainHistory
  · exact wf.valueHistory
  · exact wf.ownerBelow
  · intro d v m; rw [same] at m; exact wf.recorded d v m
  · intro d v w a b; rw [same] at a b; exact wf.domainUnique d v w a b
  · intro d e v a b; rw [same] at a b; exact wf.valueUnique d e v a b
  · apply Finset.disjoint_left.mpr
    intro entry available outgoing
    simp only [forwardPost,Finset.mem_erase] at available
    simp only [forwardPost,Finset.mem_insert] at outgoing
    rcases outgoing with same | old
    · exact available.1 same
    · exact Finset.disjoint_left.mp wf.distinctPlaces available.2 old
  · intro d v m; rw [same] at m; exact wf.separateOwners d v m
  · intro e w m consumed
    simp only [forwardPost,Finset.mem_erase] at m
    simp only [forwardPost,Finset.mem_insert] at consumed
    rcases consumed with sameValue | old
    · have sameDomain := wf.valueUnique e d w (Finset.mem_union_left _ m.2) (sameValue.symm ▸ cur)
      exact m.1 (Prod.ext sameDomain sameValue)
    · exact wf.consumedUnavailable e w m.2 old
  · intro w m
    simp only [forwardPost,Finset.mem_insert] at m
    rcases m with rfl | old
    · exact history.2
    · exact wf.consumedRecorded old
  · exact wf.noEarly

theorem forward_cannot_consume_twice {c s d v post}
    (first : Forward c s d v post) (again : State) : ¬ Forward c post d v again := by
  intro second
  rw [first.post_eq] at second
  have absent : (d,v) ∉ (forwardPost s d v).available := by simp [forwardPost]
  exact absent second.available

theorem issue_derives_fresh_unique_available {c s post} (event : Issue c s post) :
    newDomain s ∉ s.usedDomains ∧ newValue s ∉ s.usedValues ∧
    post.available = {(newDomain s,newValue s)} ∧ post.outgoing = ∅ ∧
    post.owners = s.owners ∧ post.extras = ∅ := by
  have fresh := domain_and_value_fresh event.before
  have places := no_domain_implies_places_empty event.noDomain
  rw [event.post_eq]
  exact ⟨fresh.1,fresh.2.1,by simp [issuePost,places.1],places.2,rfl,event.before.noEarly⟩

/-- Successful issuer outcome is the only entrance to this slot successor.
This is a branch dispatcher, not a new Option-returning Domain API. -/
inductive Entrance (c : Context) : OneBackingIssuerSource.Outcome → State → Prop where
  | some (owners : Custody) (history : History c) :
      Entrance c (.some (c.old.nextValue+3)) (start c owners history)

theorem none_has_no_domain_successor (c : Context) (s : State) :
    ¬ Entrance c .none s := by intro h; cases h

end
end NewLang.Adjunct.FreshDomainSource
