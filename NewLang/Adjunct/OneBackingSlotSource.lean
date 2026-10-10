import NewLang.Adjunct.OneBackingIssuerWitness
import Mathlib.Data.Finset.SDiff

/-! Issue #55: immediate successor of the accepted issuer-SPEC adjunct.
Only consuming Some, whole OneBacking destructuring, and exact Node into_slot.
No domain/typed lifetime/borrow transition or production AST claim. -/
namespace NewLang.Adjunct.OneBackingSlotSource
open F0 F1.Backing F1.Occupancy OneBackingIssuerSource
noncomputable section

/-- Read-only issuer provenance in ONE compilation-unit lineage. This is not
an additional current source Some: `Custody.current` is the sole current graph. -/
structure Context where
  target : Target
  old : Source
  ok : Success target

def Context.packet (c : Context) : Grant := freshGrant c.target c.old c.ok

inductive Phase | some | backing | raw | slot deriving DecidableEq
inductive Binding where
  | prior : OneBackingIssuerSource.Carrier → Binding
  | backingLocal | allocationLocal | rawLocal | slotLocal
  | extra : Nat → Binding
  deriving DecidableEq

/-- A second nominal is expressible only as an adversarial request. The closed
source primitive admits Node, even if another rich type has identical size. -/
inductive Request | node | other deriving DecidableEq
structure RawValue where
  id : Nat
  region : Nat
  length : Nat
  deriving DecidableEq
structure SlotValue extends RawValue where
  type : Request
  deriving DecidableEq

structure Custody where
  phase : Phase
  current : Finset (Nat × Binding)
  consumedValues : Finset Nat
  allocation : Option Nat
  raw : Option RawValue
  slot : Option SlotValue
  extras : Finset Extra

def liftEdges (edges : Finset (Nat × OneBackingIssuerSource.Carrier)) : Finset (Nat × Binding) :=
  edges.image (fun e => (e.1,Binding.prior e.2))

def frame (c : Context) : Finset (Nat × Binding) := liftEdges c.old.current

def packetGraph (c : Context) : Phase → Finset (Nat × Binding)
  | .some => liftEdges c.packet.edges
  | .backing => {(c.packet.base,.prior (.allocationMember (c.packet.base+2))),
      (c.packet.base+1,.prior (.rawMember (c.packet.base+2))),
      (c.packet.base+2,.backingLocal)}
  | .raw => {(c.packet.base,.allocationLocal),(c.packet.base+1,.rawLocal)}
  | .slot => {(c.packet.base,.allocationLocal),(c.packet.base+4,.slotLocal)}

def ended (c : Context) : Phase → Finset Nat
  | .some => ∅
  | .backing => {c.packet.base+3}
  | .raw => {c.packet.base+3,c.packet.base+2}
  | .slot => {c.packet.base+3,c.packet.base+2,c.packet.base+1}

def rawValue (c : Context) : RawValue := ⟨c.packet.base+1,c.packet.region,c.packet.n⟩
def slotValue (c : Context) : SlotValue := ⟨⟨c.packet.base+4,c.packet.region,c.packet.n⟩,.node⟩

def expectedAllocation (c : Context) : Phase → Option Nat
  | .some | .backing => none
  | .raw | .slot => some c.packet.base

def expectedRaw (c : Context) : Phase → Option RawValue
  | .raw => some (rawValue c)
  | _ => none

def expectedSlot (c : Context) : Phase → Option SlotValue
  | .slot => some (slotValue c)
  | _ => none

def UniqueCurrent (edges : Finset (Nat × Binding)) : Prop :=
  ∀ v a b, (v,a) ∈ edges → (v,b) ∈ edges → a = b

/-- Abstract current-value invariant for this fixed packet, not ready-made
matched rich authority. Every post component is proved from the updates. -/
structure SourceWF (c : Context) (s : Custody) : Prop where
  currentExact : s.current = packetGraph c s.phase ∪ frame c
  unique : UniqueCurrent s.current
  consumed : s.consumedValues = ended c s.phase
  allocation : s.allocation = expectedAllocation c s.phase
  raw : s.raw = expectedRaw c s.phase
  slot : s.slot = expectedSlot c s.phase
  noEarly : s.extras = ∅

def start (c : Context) : Custody :=
  ⟨.some,liftEdges (somePost c.target c.old c.ok).current,∅,none,none,none,c.old.extras⟩

/-- Match consumes the current Some wrapper; the very same OneBacking value
becomes an available local. Allocation/raw remain its members until destructure. -/
def matchPost (c : Context) (s : Custody) : Custody :=
  {s with
    phase := .backing
    current := ((s.current.erase (c.packet.base+3,.prior (.result (c.packet.base+3)))).erase
      (c.packet.base+2,.prior (.someMember (c.packet.base+3)))) ∪
        {(c.packet.base+2,.backingLocal)}
    consumedValues := insert (c.packet.base+3) s.consumedValues}

/-- Whole destructure consumes OneBacking and moves its TWO nonCopy members
into separate available locals. No second original A/raw is issued. -/
def destructurePost (c : Context) (s : Custody) : Custody :=
  {s with
    phase := .raw
    current := (((s.current.erase (c.packet.base,.prior (.allocationMember (c.packet.base+2)))).erase
      (c.packet.base+1,.prior (.rawMember (c.packet.base+2)))).erase (c.packet.base+2,.backingLocal)) ∪
        {(c.packet.base,.allocationLocal),(c.packet.base+1,.rawLocal)}
    consumedValues := insert (c.packet.base+2) s.consumedValues
    allocation := some c.packet.base
    raw := some (rawValue c)}

/-- into_slot consumes the raw value and creates a fresh EMPTY slot value.
A remains the same separate available value; region/length remain unchanged. -/
def slotPost (c : Context) (s : Custody) : Custody :=
  {s with
    phase := .slot
    current := (s.current.erase (c.packet.base+1,.rawLocal)) ∪
      {(c.packet.base+4,.slotLocal)}
    consumedValues := insert (c.packet.base+1) s.consumedValues
    raw := none
    slot := some (slotValue c)}

inductive Step (c : Context) : Custody → Custody → Prop where
  | matchSome (s : Custody) (wf : SourceWF c s) (phase : s.phase = .some) :
      Step c s (matchPost c s)
  | destructure (s : Custody) (wf : SourceWF c s) (phase : s.phase = .backing) :
      Step c s (destructurePost c s)
  | intoSlot (s : Custody) (wf : SourceWF c s) (phase : s.phase = .raw)
      (size : c.packet.n = c.target.sizeofH)
      (alignment : c.packet.observedAddress % c.target.alignofH = 0) :
      Step c s (slotPost c s)

/-- The typed spelling check is distinct from rich layout-size equality. -/
def AdmittedRequest (request : Request) : Prop := request = .node

/-- Source nominal admission is part of this abstract specification, not inferred
from an equal-size rich claim or from a production checker. -/
def IntoSlotRequest (c : Context) (request : Request) (s post : Custody) : Prop :=
  AdmittedRequest request ∧ s.phase = .raw ∧ Step c s post

/-- Only a successful issuer result can be dispatched into this successor. -/
inductive Dispatch (c : Context) : Outcome → Custody → Prop where
  | some : Dispatch c (.some (c.old.nextValue+3)) (start c)

theorem none_has_no_successor (c : Context) (s : Custody) : ¬ Dispatch c .none s := by
  intro h; cases h

theorem other_request_rejected (c : Context) (s post : Custody) :
    ¬ IntoSlotRequest c .other s post := by
  rintro ⟨h,_,_⟩; cases h

theorem issuer_derives_size_alignment (c : Context) :
    c.packet.n = c.target.sizeofH ∧
    c.packet.observedAddress % c.target.alignofH = 0 := ⟨rfl,c.ok.aligned⟩

theorem lift_union (a b : Finset (Nat × OneBackingIssuerSource.Carrier)) :
    liftEdges (a ∪ b) = liftEdges a ∪ liftEdges b := Finset.image_union _ _

theorem frame_value_below {c} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    {v b} (edge : (v,b) ∈ frame c) : v < c.packet.base := by
  rcases Finset.mem_image.mp edge with ⟨⟨w,k⟩,member,eq⟩
  have same := congrArg Prod.fst eq
  simp only at same; subst w
  exact old_current_below oldWF member

theorem frame_has_no_new_value {c} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    {v b} (fresh : c.packet.base ≤ v) : (v,b) ∉ frame c := by
  intro edge; have := frame_value_below oldWF edge; omega

theorem packet_graph_bounds (c : Context) (phase : Phase) {v b}
    (edge : (v,b) ∈ packetGraph c phase) : c.packet.base ≤ v := by
  cases phase with
  | some =>
    rcases Finset.mem_image.mp edge with ⟨⟨w,k⟩,member,eq⟩
    have same := congrArg Prod.fst eq
    simp only at same; subst w
    exact (edges_bounds _ member).1
  | backing =>
    simp [packetGraph] at edge
    rcases edge with edge | edge | edge <;> rcases edge with ⟨rfl,_⟩ <;> omega
  | raw | slot =>
    simp [packetGraph] at edge
    rcases edge with edge | edge <;> rcases edge with ⟨rfl,_⟩ <;> omega

theorem packet_graph_unique (c : Context) (phase : Phase) : UniqueCurrent (packetGraph c phase) := by
  intro v a b ha hb
  cases phase with
  | some =>
    rcases Finset.mem_image.mp ha with ⟨⟨va,ca⟩,ma,ea⟩
    rcases Finset.mem_image.mp hb with ⟨⟨vb,cb⟩,mb,eb⟩
    have := congrArg Prod.fst ea; simp only at this; subst va
    have := congrArg Prod.fst eb; simp only at this; subst vb
    have eq := edges_unique c.packet v ca cb ma mb
    exact (congrArg Prod.snd ea).symm.trans ((congrArg Binding.prior eq).trans (congrArg Prod.snd eb))
  | backing =>
    simp [packetGraph] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      rcases ha with ⟨hv,ha⟩ <;> rcases hb with ⟨hw,hb⟩ <;> simp_all
  | raw | slot =>
    simp [packetGraph] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases ha with ⟨hv,ha⟩ <;> rcases hb with ⟨hw,hb⟩ <;> simp_all

theorem framed_current_unique {c} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (phase : Phase) : UniqueCurrent (packetGraph c phase ∪ frame c) := by
  intro v a b ha hb
  rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
  · exact packet_graph_unique c phase v a b ha hb
  · have := packet_graph_bounds c phase ha; have := frame_value_below oldWF hb; omega
  · have := packet_graph_bounds c phase hb; have := frame_value_below oldWF ha; omega
  · rcases Finset.mem_image.mp ha with ⟨⟨va,ca⟩,ma,ea⟩
    rcases Finset.mem_image.mp hb with ⟨⟨vb,cb⟩,mb,eb⟩
    have := congrArg Prod.fst ea; simp only at this; subst va
    have := congrArg Prod.fst eb; simp only at this; subst vb
    have eq := oldWF.unique v ca cb ma mb
    exact (congrArg Prod.snd ea).symm.trans ((congrArg Binding.prior eq).trans (congrArg Prod.snd eb))

theorem start_wellFormed {c} (oldWF : OneBackingIssuerSource.SourceWF c.old) : SourceWF c (start c) := by
  constructor
  · exact lift_union _ _
  · rw [show (start c).current = packetGraph c .some ∪ frame c from lift_union _ _]
    exact framed_current_unique oldWF .some
  · rfl
  · rfl
  · rfl
  · rfl
  · exact oldWF.noEarly

/-- Erasing a fresh packet value never consumes an older C frame edge. -/
theorem erase_frame {c} (oldWF : OneBackingIssuerSource.SourceWF c.old) {v b}
    (fresh : c.packet.base ≤ v) : (frame c).erase (v,b) = frame c :=
  Finset.erase_eq_of_notMem (frame_has_no_new_value oldWF fresh)

theorem match_graph (c : Context) :
    ((packetGraph c .some).erase (c.packet.base+3,.prior (.result (c.packet.base+3)))).erase
      (c.packet.base+2,.prior (.someMember (c.packet.base+3))) ∪ {(c.packet.base+2,.backingLocal)} =
    packetGraph c .backing := by
  simp [packetGraph,liftEdges,Grant.edges,Finset.erase_insert_of_ne]

theorem destructure_graph (c : Context) :
    (((packetGraph c .backing).erase (c.packet.base,.prior (.allocationMember (c.packet.base+2)))).erase
      (c.packet.base+1,.prior (.rawMember (c.packet.base+2)))).erase (c.packet.base+2,.backingLocal) ∪
      {(c.packet.base,.allocationLocal),(c.packet.base+1,.rawLocal)} = packetGraph c .raw := by
  simp [packetGraph]

theorem slot_graph (c : Context) :
    (packetGraph c .raw).erase (c.packet.base+1,.rawLocal) ∪ {(c.packet.base+4,.slotLocal)} =
    packetGraph c .slot := by
  simp [packetGraph,Finset.erase_insert_of_ne]

theorem match_current_frame {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .some) :
    (matchPost c s).current = packetGraph c .backing ∪ frame c := by
  simp only [matchPost,wf.currentExact,phase,Finset.erase_union_distrib]
  rw [erase_frame oldWF (by omega),erase_frame oldWF (by omega)]
  rw [Finset.union_right_comm,match_graph]

theorem destructure_current_frame {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .backing) :
    (destructurePost c s).current = packetGraph c .raw ∪ frame c := by
  simp only [destructurePost,wf.currentExact,phase,Finset.erase_union_distrib]
  rw [erase_frame oldWF (by omega),erase_frame oldWF (by omega),erase_frame oldWF (by omega)]
  rw [Finset.union_right_comm,destructure_graph]

theorem slot_current_frame {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .raw) :
    (slotPost c s).current = packetGraph c .slot ∪ frame c := by
  simp only [slotPost,wf.currentExact,phase,Finset.erase_union_distrib]
  rw [erase_frame oldWF (by omega),Finset.union_right_comm,slot_graph]

theorem match_wellFormed {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .some) : SourceWF c (matchPost c s) := by
  constructor
  · exact match_current_frame oldWF wf phase
  · rw [match_current_frame oldWF wf phase]; exact framed_current_unique oldWF .backing
  · simp [matchPost,wf.consumed,phase,ended]
  · simpa [matchPost,phase,expectedAllocation] using wf.allocation
  · simpa [matchPost,phase,expectedRaw] using wf.raw
  · simpa [matchPost,phase,expectedSlot] using wf.slot
  · exact wf.noEarly

theorem destructure_wellFormed {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .backing) : SourceWF c (destructurePost c s) := by
  constructor
  · exact destructure_current_frame oldWF wf phase
  · rw [destructure_current_frame oldWF wf phase]; exact framed_current_unique oldWF .raw
  · simp only [destructurePost,wf.consumed,phase,ended]; exact Finset.insert_comm (c.packet.base+2) (c.packet.base+3) (∅ : Finset Nat)
  · rfl
  · rfl
  · simpa [destructurePost,phase,expectedSlot] using wf.slot
  · exact wf.noEarly

theorem slot_wellFormed {c s} (oldWF : OneBackingIssuerSource.SourceWF c.old)
    (wf : SourceWF c s) (phase : s.phase = .raw) : SourceWF c (slotPost c s) := by
  constructor
  · exact slot_current_frame oldWF wf phase
  · rw [slot_current_frame oldWF wf phase]; exact framed_current_unique oldWF .slot
  · simp only [slotPost,wf.consumed,phase,ended]; ext n; simp [or_assoc,or_comm]
  · simpa [slotPost,phase,expectedAllocation] using wf.allocation
  · rfl
  · rfl
  · exact wf.noEarly

theorem every_step_preserves_source_wellFormed {c s post}
    (oldWF : OneBackingIssuerSource.SourceWF c.old) (step : Step c s post) : SourceWF c post := by
  cases step with
  | matchSome wf phase => exact match_wellFormed oldWF wf phase
  | destructure wf phase => exact destructure_wellFormed oldWF wf phase
  | intoSlot wf phase _ _ => exact slot_wellFormed oldWF wf phase

end
end NewLang.Adjunct.OneBackingSlotSource
