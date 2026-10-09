import NewLang.Adjunct.FiveRoot

namespace NewLang.Adjunct.FiveRoot
open F0 F1.Backing F1.Occupancy
noncomputable section

theorem site_code_injective : Function.Injective Site.code := by
  intro i j eq; cases i <;> cases j <;> simp [Site.code] at eq ⊢
theorem field_code_injective : Function.Injective Field.code := by
  intro i j eq; cases i <;> cases j <;> simp [Field.code] at eq ⊢
theorem projection_injective : Function.Injective projection := by
  intro f g eq; apply field_code_injective; exact congrArg ProjectionId.index eq

theorem field_place_injective {i j f g} (eq : fieldPlace i f = fieldPlace j g) : i = j ∧ f = g := by
  have same := congrArg PlaceId.index eq
  cases i <;> cases j <;> cases f <;> cases g <;> simp [fieldPlace,Site.code,Field.code] at same ⊢
theorem parent_place_injective : Function.Injective parentPlace := by
  intro i j eq; apply site_code_injective
  have same := congrArg PlaceId.index eq; dsimp [parentPlace] at same; omega
theorem parent_ne_field (i j : Site) (f : Field) : parentPlace i ≠ fieldPlace j f := by
  cases i <;> cases j <;> cases f <;> decide

theorem original_region_injective (w : LiveTail.WorldId) : Function.Injective (fun i => (original w i).region) := by
  intro i j eq; apply site_code_injective
  have same := congrArg BackingRegionId.index eq; dsimp [original] at same; omega
theorem original_incarnation_injective (w : LiveTail.WorldId) : Function.Injective (fun i => (original w i).ptr.incarnation) := by
  intro i j eq; apply site_code_injective
  have same := congrArg IncarnationId.index eq; dsimp [original] at same; omega
theorem original_domain_injective (w : LiveTail.WorldId) : Function.Injective (fun i => (original w i).domain) := by
  intro i j eq; apply site_code_injective
  have same := congrArg DomainId.index eq; dsimp [original] at same; omega
theorem original_allocation_injective (w : LiveTail.WorldId) : Function.Injective (fun i => (original w i).allocation) := by
  intro i j eq; apply site_code_injective
  have same := congrArg F2.BindingId.index eq; dsimp [original] at same; omega

theorem qualified_origin_reconstruction {w v i j a b}
    (qa : reconstruct w i a) (qb : reconstruct v j b) (same : a = b) : w = v ∧ i = j := by
  rw [qa,qb] at same
  refine ⟨congrArg Origin.world same,?_⟩
  have worlds : w = v := congrArg Origin.world same; subst v
  exact original_region_injective w (congrArg Origin.region same)

/-- Actual fixed siblings within ONE root; use the reviewed structural theorem. -/
theorem fields_are_known_disjoint (i : Site) {f g : Field} (distinct : f ≠ g) :
    F1.KnownDisjoint (layout i) (fieldPlace i f) (fieldPlace i g) := by
  apply F1.known_disjoint_siblings_do_not_overlap
  refine ⟨fun eq => distinct (field_place_injective eq).2,parentPlace i,?_,?_⟩
  · refine ⟨by simp [layout],?_,f.code,?_⟩
    · cases f <;> simp [layout]
    · cases i <;> cases f <;> decide
  · refine ⟨by simp [layout],?_,g.code,?_⟩
    · cases g <;> simp [layout]
    · cases i <;> cases g <;> decide

private theorem typed_present {s i} (live : Typed s i) : ∃ c, s.cell i = some c := by
  rcases live with ⟨c,eq,_⟩; exact ⟨c,eq⟩

private theorem allocation_memory {s i o} (step : Allocate s i o) : MemoryInvariant (allocatePost s i o) := by
  have m := step.pre.memory
  have absent : s.cell i = none := by
    cases eq : s.cell i with
    | none => rfl
    | some c => have lt := (m.allocatedPrefix i).mp ⟨c,eq⟩; rw [step.next] at lt; omega
  have maxCode : i.code ≤ 4 := by cases i <;> decide
  have next := step.next
  refine ⟨by dsimp [allocatePost]; omega,?_,?_,?_⟩
  · intro j; by_cases same : j = i
    · subst j; simp [allocatePost,step.next]
    · have neqCode : j.code ≠ s.successes := by intro eq; exact same (site_code_injective (eq.trans step.next.symm))
      simp only [allocatePost,same,↓reduceIte,m.allocatedPrefix j]
      omega
  · intro j none; by_cases same : j = i
    · subst j; simp [allocatePost] at none
    · simpa [allocatePost,same] using m.absent j (by simpa [allocatePost,same] using none)
  · intro j c present; by_cases same : j = i
    · subst j
      have eq : KnownCall.Cell.mk .typed true 0 = c := Option.some.inj (by simpa [allocatePost] using present)
      subst c
      simpa [allocatePost,expectedOwners,expectedClaim] using step.source
    · simpa [allocatePost,same] using m.present j c (by simpa [allocatePost,same] using present)

private theorem allocation_fields {s i o} (step : Allocate s i o) : FieldInvariant (allocatePost s i o) := by
  have h := step.pre.fields
  have oldLive : ∀ j, j ≠ i → Typed (allocatePost s i o) j → Typed s j := by
    intro j ne live; simpa [Typed,allocatePost,ne] using live
  constructor
  · intro j live; by_cases same : j = i
    · subst j; exact Finset.mem_union_right _ (by simp [allocatePost,initialFacts])
    · exact Finset.mem_union_left _ (by simpa [allocatePost,same] using h.parentRecorded j (oldLive j same live))
  · intro j live f; by_cases same : j = i
    · subst j; apply Finset.mem_union_right; cases f <;> simp [allocatePost,initialFacts]
    · exact Finset.mem_union_left _ (by simpa [allocatePost,same] using h.fieldsRecorded j (oldLive j same live) f)
  · intro j live f; by_cases same : j = i
    · subst j; simp [allocatePost,initialLink]
    · simpa [allocatePost,same] using h.shape j (oldLive j same live) f
  · intro j live f occ present; by_cases same : j = i
    · subst j; simp [allocatePost,initialLink] at present
    · exact h.occurrencesRecorded j (oldLive j same live) f occ (by simpa [allocatePost,same] using present)
  · intro j live f vf present; by_cases same : j = i
    · subst j; simp [allocatePost,initialLink] at present
    · exact Finset.mem_union_left _ (h.payloadRecorded j (oldLive j same live) f vf (by simpa [allocatePost,same] using present))
  · intro j k jl kl f g occ je ke
    by_cases ji : j = i
    · subst j; simp [allocatePost,initialLink] at je
    by_cases ki : k = i
    · subst k; simp [allocatePost,initialLink] at ke
    exact h.occurrencesUnique j k (oldLive j ji jl) (oldLive k ki kl) f g occ
      (by simpa [allocatePost,ji] using je) (by simpa [allocatePost,ki] using ke)

theorem allocation_preserves_wellFormed {s i o} (step : Allocate s i o) : WellFormed (allocatePost s i o) := by
  refine ⟨allocation_memory step,allocation_fields step,?_⟩
  simp [DependenciesValid,allocatePost,step.noObservers]

theorem allocation_has_one_original_pair {s i o} (step : Allocate s i o) :
    (allocatePost s i o).origin i = original s.world i ∧
    (allocatePost s i o).owners i = [.allocation o,.domain o] ∧
    (allocatePost s i o).claim i = some (.root ⟨0⟩ o.ptr.location (full o)) :=
  by simpa [allocatePost,reconstruct] using step.source

theorem allocation_preserves_previous_origin {s i o} (_step : Allocate s i o) {j} (other : j ≠ i) :
    (allocatePost s i o).origin j = s.origin j ∧ (allocatePost s i o).cell j = s.cell j ∧
    (allocatePost s i o).owners j = s.owners j ∧ (allocatePost s i o).claim j = s.claim j := by
  simp [allocatePost,other]

theorem mode_preserving_projection {s i f r} (valid : FieldRefValid s i f r) :
    r.projection = projection f ∧ RootRefValid s i r.base := ⟨valid.2.2,valid.1⟩
theorem readonly_projection_cannot_write {s i f r value p} (readOnly : r.base.mode.write = false) :
    ¬ Replace s i f r value p := by intro h; have w := h.write; rw [readOnly] at w; cases w

theorem change_preserves_original_memory (s : State) (i : Site) (f : Field) (v) (p : ChangePlan) :
    (changePost s i f v p).cell = s.cell ∧ (changePost s i f v p).origin = s.origin ∧
    (changePost s i f v p).owners = s.owners ∧ (changePost s i f v p).claim = s.claim := ⟨rfl,rfl,rfl,rfl⟩
theorem change_frames_sibling (s : State) (i : Site) {f g : Field} (other : g ≠ f) (v) (p : ChangePlan) :
    (changePost s i f v p).link i g = s.link i g := by simp [changePost,other]
theorem change_frames_other_root (s : State) {i j : Site} (other : j ≠ i) (f) (v) (p : ChangePlan) :
    (changePost s i f v p).parentFact j = s.parentFact j ∧
    (changePost s i f v p).link j = s.link j := by simp [changePost,other]

private theorem change_history (s : State) (i : Site) (f : Field) (v) (p : ChangePlan) :
    s.usedFacts ⊆ (changePost s i f v p).usedFacts ∧
    s.usedOccurrences ⊆ (changePost s i f v p).usedOccurrences := by
  constructor
  · intro a mem; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
  · cases v <;> simp [changePost]

private theorem change_fields {s i f r v p} (step : Replace s i f r v p) :
    FieldInvariant (changePost s i f v p) := by
  have h := step.pre.fields
  have hist := change_history s i f v p
  constructor
  · intro j live; by_cases same : j = i
    · subst j; simp [changePost]
    · exact hist.1 (by simpa [changePost,same] using h.parentRecorded j live)
  · intro j live g; by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; simp [changePost]
    · exact hist.1 (by simpa [changePost,same] using h.fieldsRecorded j live g)
  · intro j live g; by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; cases v <;> simp [changePost]
    · simpa [changePost,same] using h.shape j live g
  · intro j live g occ present; by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; cases v <;> simp [changePost] at present ⊢
      subst occ; simp
    · exact hist.2 (h.occurrencesRecorded j live g occ (by simpa [changePost,same] using present))
  · intro j live g vf present; by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; cases v <;> simp [changePost] at present ⊢
      subst vf; simp
    · exact hist.1 (h.payloadRecorded j live g vf (by simpa [changePost,same] using present))
  · intro j k jl kl g hfield occ je ke
    by_cases left : j = i ∧ g = f
    · rcases left with ⟨leftSite,leftField⟩; subst j; subst g
      cases v with
      | none => simp [changePost] at je
      | some ptr =>
        have eq : p.occurrence = occ := Option.some.inj (by simpa [changePost] using je)
        by_cases right : k = i ∧ hfield = f
        · exact ⟨right.1.symm,right.2.symm⟩
        · have old := h.occurrencesRecorded k kl hfield occ (by simpa [changePost,right] using ke)
          exact False.elim (step.fresh.2.2.2.2.2.2 (eq ▸ old))
    · by_cases right : k = i ∧ hfield = f
      · rcases right with ⟨rightSite,rightField⟩; subst k; subst hfield
        cases v with
        | none => simp [changePost] at ke
        | some ptr =>
          have eq : p.occurrence = occ := Option.some.inj (by simpa [changePost] using ke)
          have old := h.occurrencesRecorded j jl g occ (by simpa [changePost,left] using je)
          exact False.elim (step.fresh.2.2.2.2.2.2 (eq ▸ old))
      · exact h.occurrencesUnique j k jl kl g hfield occ
          (by simpa [changePost,left] using je) (by simpa [changePost,right] using ke)

private theorem change_live_fact {s i f r v p fact} (step : Replace s i f r v p)
    (live : FactLive s fact) (safe : ¬ Affected s i f fact) : FactLive (changePost s i f v p) fact := by
  cases fact with
  | fixed fact =>
    cases fact with
    | domainLive d => exact live
    | valueFact place vf =>
      rcases live with ⟨j,jl,parent|⟨g,gp,gv⟩⟩
      · by_cases same : j = i
        · subst j; exact False.elim (safe (Or.inl parent))
        · exact ⟨j,jl,Or.inl ⟨parent.1,by simpa [changePost,same] using parent.2⟩⟩
      · by_cases same : j = i ∧ g = f
        · rcases same with ⟨rfl,rfl⟩; exact False.elim (safe (Or.inr ⟨gp,gv⟩))
        · exact ⟨j,jl,Or.inr ⟨g,gp,by simpa [changePost,same] using gv⟩⟩
  | occurrence occ =>
    rcases live with ⟨j,jl,g,eq⟩
    by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; exact False.elim (safe eq)
    · exact ⟨j,jl,g,by simpa [changePost,same] using eq⟩
  | payloadValue occ vf =>
    rcases live with ⟨j,jl,g,eq,payload⟩
    by_cases same : j = i ∧ g = f
    · rcases same with ⟨rfl,rfl⟩; exact False.elim (safe ⟨eq,payload⟩)
    · exact ⟨j,jl,g,by simpa [changePost,same] using eq,by simpa [changePost,same] using payload⟩

theorem change_preserves_wellFormed {s i f r v p} (step : Replace s i f r v p) : WellFormed (changePost s i f v p) := by
  have m := step.pre.memory
  refine ⟨⟨m.bounded,m.allocatedPrefix,m.absent,m.present⟩,change_fields step,?_⟩
  intro fact dep; exact change_live_fact step (step.pre.dependencies fact dep) (step.guard.2 fact dep)

theorem some_to_some_starts_fresh_occurrence {s i f r ptr p old}
    (step : Replace s i f r (some ptr) p) (before : (s.link i f).occurrence = some old) :
    (changePost s i f (some ptr) p).link i f = ⟨some ptr,p.field,some p.occurrence,some p.payload⟩ ∧
    p.occurrence ≠ old ∧ p.occurrence ∈ (changePost s i f (some ptr) p).usedOccurrences := by
  refine ⟨by simp [changePost],?_,Finset.mem_insert_self _ _⟩
  intro eq; apply step.fresh.2.2.2.2.2.2
  exact eq ▸ step.pre.fields.occurrencesRecorded i step.ref.1.2.2.2.1 f old before

theorem occurrence_dependency_rejects_reset {s i f r v p old}
    (present : (s.link i f).occurrence = some old)
    (dep : F1.Conditional.Fact.occurrence old ∈ s.dependencies) : ¬ Replace s i f r v p := by
  intro step; exact step.guard.2 _ dep present

theorem unknown_alias_never_grants_replace {s i f r v p} (unknown : s.unknownAlias = true) :
    ¬ Replace s i f r v p := by intro step; have g := step.guard.1; rw [unknown] at g; cases g

theorem wrong_projection_never_grants_replace {s i f r v p} (wrong : r.projection ≠ projection f) :
    ¬ Replace s i f r v p := by intro step; exact wrong step.ref.2.2

/-- Opening/closing a bounded scoped loan does not mint A/D or change any value. -/
def withLoans (s : State) (loans : Finset Site) : State := {s with loans := loans}
theorem withLoans_wellFormed {s : State} (h : WellFormed s) (loans : Finset Site) :
    WellFormed (withLoans s loans) :=
  ⟨⟨h.memory.bounded,h.memory.allocatedPrefix,h.memory.absent,h.memory.present⟩,
    ⟨h.fields.parentRecorded,h.fields.fieldsRecorded,h.fields.shape,h.fields.occurrencesRecorded,
      h.fields.payloadRecorded,h.fields.occurrencesUnique⟩,h.dependencies⟩

private theorem typed_cell {s i} (h : WellFormed s) (t : Typed s i) :
    s.cell i = some ⟨.typed,true,0⟩ := by
  rcases t with ⟨c,eq,phase⟩
  have m := h.memory.present i c eq
  have domain := m.2.2.2.2.1 phase
  have count : c.releases = 0 := by simpa [phase] using m.2.2.2.1
  cases c; simp_all

theorem cleanup_available {s i} (h : WellFormed s) (t : Typed s i) (guard : EndGuard s i) :
    Cleanup s i (s.origin i) (s.origin i) (full (s.origin i)) := by
  have cell := typed_cell h t
  have own := (h.memory.present i _ cell).2.1
  simp only [expectedOwners,↓reduceIte] at own
  refine ⟨h,⟨t,?_,guard⟩,?_,?_,?_⟩
  · simp [own]
  · exact ⟨⟨.emptySlot,true,0⟩,by simp [endPost,cell],rfl⟩
  · refine ⟨⟨⟨.raw,true,0⟩,by simp [erasePost,endPost,cell],rfl,rfl⟩,?_⟩
    simp [erasePost,endPost,own]
  · refine ⟨⟨⟨.raw,false,0⟩,by simp [finalizePost,erasePost,endPost,cell],rfl,rfl,rfl⟩,?_,rfl,rfl⟩
    simp [finalizePost,erasePost,endPost,own]

theorem endRoot_requires_original_domain {s i d} (h : WellFormed s) (step : CanEnd s i d) :
    d = s.origin i := by
  have cell := typed_cell h step.1
  have own := (h.memory.present i _ cell).2.1
  simpa [own,expectedOwners] using step.2.1

theorem release_requires_original_allocation {s i a raw} (h : CanRelease s i a raw) :
    a = s.origin i ∧ raw = full a := h.2.2

theorem cleanup_target {s i d a raw} (step : Cleanup s i d a raw) :
    (cleanupPost s i).cell i = some ⟨.released,false,1⟩ ∧
    (cleanupPost s i).owners i = [] ∧ (cleanupPost s i).claim i = none ∧
    (cleanupPost s i).origin i = s.origin i := by
  have cell := typed_cell step.pre step.endRoot.1
  simp [cleanupPost,releasePost,finalizePost,erasePost,endPost,cell]

theorem cleanup_frames_other_root (s : State) {i j : Site} (ne : j ≠ i) :
    (cleanupPost s i).cell j = s.cell j ∧ (cleanupPost s i).owners j = s.owners j ∧
    (cleanupPost s i).claim j = s.claim j ∧ (cleanupPost s i).origin j = s.origin j := by
  simp [cleanupPost,releasePost,finalizePost,erasePost,endPost,ne]

private theorem cleanup_typed_iff {s i d a raw} (step : Cleanup s i d a raw) (j : Site) :
    Typed (cleanupPost s i) j ↔ j ≠ i ∧ Typed s j := by
  by_cases ne : j = i
  · subst j; simp [Typed,(cleanup_target step).1]
  · simp [Typed,cleanup_frames_other_root s ne,ne]

private theorem cleanup_domain_iff {s i d a raw} (step : Cleanup s i d a raw) (j : Site) :
    DomainAlive (cleanupPost s i) j ↔ j ≠ i ∧ DomainAlive s j := by
  by_cases ne : j = i
  · subst j; simp [DomainAlive,(cleanup_target step).1]
  · simp [DomainAlive,cleanup_frames_other_root s ne,ne]

private theorem cleanup_memory {s i d a raw} (step : Cleanup s i d a raw) : MemoryInvariant (cleanupPost s i) := by
  have m := step.pre.memory
  have before := typed_cell step.pre step.endRoot.1
  have target := cleanup_target step
  constructor
  · exact m.bounded
  · intro j
    change (∃ c, (cleanupPost s i).cell j = some c) ↔ j.code < s.successes
    by_cases same : j = i
    · subst j
      have old := (m.allocatedPrefix i).mp ⟨_,before⟩
      simp [target.1,old]
    · simpa [(cleanup_frames_other_root s same).1] using m.allocatedPrefix j
  · intro j absent; by_cases same : j = i
    · subst j; rw [target.1] at absent; cases absent
    · simpa [(cleanup_frames_other_root s same).2.1,(cleanup_frames_other_root s same).2.2.1] using
        m.absent j (by simpa [(cleanup_frames_other_root s same).1] using absent)
  · intro j c eq; by_cases same : j = i
    · subst j
      have eqc : KnownCall.Cell.mk .released false 1 = c := Option.some.inj (target.1.symm.trans eq)
      subst c
      have origin := (m.present i _ before).1
      simpa [cleanupPost,releasePost,finalizePost,erasePost,endPost,expectedOwners,expectedClaim] using origin
    · simpa [cleanupPost,releasePost,finalizePost,erasePost,endPost,same] using
        m.present j c (by simpa [(cleanup_frames_other_root s same).1] using eq)

private theorem cleanup_fields {s i d a raw} (step : Cleanup s i d a raw) : FieldInvariant (cleanupPost s i) := by
  have h := step.pre.fields
  constructor
  · intro j t; exact h.parentRecorded j ((cleanup_typed_iff step j).mp t).2
  · intro j t f; exact h.fieldsRecorded j ((cleanup_typed_iff step j).mp t).2 f
  · intro j t f; exact h.shape j ((cleanup_typed_iff step j).mp t).2 f
  · intro j t f o eq; exact h.occurrencesRecorded j ((cleanup_typed_iff step j).mp t).2 f o eq
  · intro j t f vf eq; exact h.payloadRecorded j ((cleanup_typed_iff step j).mp t).2 f vf eq
  · intro j k tj tk f g o ej ek
    exact h.occurrencesUnique j k ((cleanup_typed_iff step j).mp tj).2
      ((cleanup_typed_iff step k).mp tk).2 f g o ej ek

private theorem cleanup_dependencies {s i d a raw} (step : Cleanup s i d a raw) : DependenciesValid (cleanupPost s i) := by
  intro fact dep
  have live := step.pre.dependencies fact dep
  have safe := step.endRoot.2.2.2.2 fact dep
  cases fact with
  | fixed fact =>
    cases fact with
    | domainLive domain =>
      rcases live with ⟨j,jl,eq⟩
      have other : j ≠ i := by intro same; subst j; exact safe eq
      exact ⟨j,(cleanup_domain_iff step j).mpr ⟨other,jl⟩,eq⟩
    | valueFact place vf =>
      rcases live with ⟨j,jl,parent|⟨f,eq,fact⟩⟩
      · have other : j ≠ i := by intro same; subst j; exact safe.1 parent.1
        exact ⟨j,(cleanup_typed_iff step j).mpr ⟨other,jl⟩,Or.inl parent⟩
      · have other : j ≠ i := by intro same; subst j; exact safe.2 f eq
        exact ⟨j,(cleanup_typed_iff step j).mpr ⟨other,jl⟩,Or.inr ⟨f,eq,fact⟩⟩
  | occurrence o =>
    rcases live with ⟨j,jl,f,eq⟩
    have other : j ≠ i := by intro same; subst j; exact safe f eq
    exact ⟨j,(cleanup_typed_iff step j).mpr ⟨other,jl⟩,f,eq⟩
  | payloadValue o vf =>
    rcases live with ⟨j,jl,f,eq,veq⟩
    have other : j ≠ i := by intro same; subst j; exact safe f eq
    exact ⟨j,(cleanup_typed_iff step j).mpr ⟨other,jl⟩,f,eq,veq⟩

theorem cleanup_preserves_wellFormed {s i d a raw} (step : Cleanup s i d a raw) :
    WellFormed (cleanupPost s i) :=
  ⟨cleanup_memory step,cleanup_fields step,cleanup_dependencies step⟩

/-- One original responsibility moves root -> slot -> full raw, A survives until
release and D survives until finalize; no duplicated simultaneous claim. -/
theorem root_slot_raw_conservation {s i d a raw} (step : Cleanup s i d a raw) :
    (endPost s i).claim i = some (.slot ⟨0⟩ (full (s.origin i))) ∧
    (endPost s i).owners i = s.owners i ∧
    (erasePost (endPost s i) i).claim i = some (.storage (full (s.origin i))) ∧
    (finalizePost (erasePost (endPost s i) i) i).owners i = [.allocation (s.origin i)] ∧
    a = s.origin i ∧ d = s.origin i := by
  have own := (step.pre.memory.present i _ (typed_cell step.pre step.endRoot.1)).2.1
  refine ⟨by simp [endPost],rfl,by simp [erasePost,endPost],?_,step.release.2.2.1,endRoot_requires_original_domain step.pre step.endRoot⟩
  simp [finalizePost,erasePost,endPost,own,expectedOwners]

theorem double_release_rejected {s i d a raw b extent} (step : Cleanup s i d a raw) :
    ¬ CanRelease (cleanupPost s i) i b extent := by
  intro again
  rcases again.1 with ⟨c,eq,phase,_⟩
  have same := Option.some.inj ((cleanup_target step).1.symm.trans eq)
  subst c; cases phase

/-- Candidate dependency failure is derived, not assumed as a post-state oracle. -/
theorem changed_old_occurrence_not_live {s i f r v p old}
    (step : Replace s i f r v p) (before : (s.link i f).occurrence = some old) :
    ¬ FactLive (changePost s i f v p) (.occurrence old) := by
  rintro ⟨j,live,g,present⟩
  by_cases selected : j = i ∧ g = f
  · rcases selected with ⟨ji,gf⟩; subst j; subst g
    cases v with
    | none => simp [changePost] at present
    | some ptr =>
      have eq : p.occurrence = old := Option.some.inj (by simpa [changePost] using present)
      exact step.fresh.2.2.2.2.2.2 (eq ▸ step.pre.fields.occurrencesRecorded i step.ref.1.2.2.2.1 f old before)
  · have prior : (s.link j g).occurrence = some old := by simpa [changePost,selected] using present
    have same := step.pre.fields.occurrencesUnique i j step.ref.1.2.2.2.1 live f g old before prior
    exact selected ⟨same.1.symm,same.2.symm⟩

theorem selected_old_current_fact_not_live {s i f r v p}
    (step : Replace s i f r v p) :
    ¬ FactLive (changePost s i f v p) (.fixed (.valueFact (fieldPlace i f) (s.link i f).currentFact)) := by
  rintro ⟨j,_,parent|⟨g,place,fact⟩⟩
  · exact parent_ne_field j i f parent.1.symm
  · have same := field_place_injective place
    rcases same with ⟨ji,fg⟩; subst j; subst g
    have eq : (s.link i f).currentFact = p.field := by simpa [changePost] using fact
    exact step.fresh.2.1 (eq ▸ step.pre.fields.fieldsRecorded i step.ref.1.2.2.2.1 f)

theorem ancestor_old_current_fact_not_live {s i f r v p}
    (step : Replace s i f r v p) :
    ¬ FactLive (changePost s i f v p) (.fixed (.valueFact (parentPlace i) (s.parentFact i))) := by
  rintro ⟨j,_,parent|⟨g,place,_⟩⟩
  · have same := parent_place_injective parent.1; subst j
    have eq : s.parentFact i = p.parent := by simpa [changePost] using parent.2
    exact step.fresh.1 (eq ▸ step.pre.fields.parentRecorded i step.ref.1.2.2.2.1)
  · exact parent_ne_field i j g place

/-- This structural projection retains the parent's exact domain/incarnation. -/
theorem field_ref_has_parent_identity {s i f r} (valid : FieldRefValid s i f r) :
    r.base.ptr.incarnation = (s.origin i).ptr.incarnation ∧
    r.base.domain = (s.origin i).domain ∧
    F1.role (layout i) (fieldPlace i f) = .fixedSubobject := by
  refine ⟨congrArg PtrToken.incarnation valid.1.2.1,valid.1.2.2.1,?_⟩
  simp [F1.role,layout,(parent_ne_field i i f).symm]

theorem copied_option_has_no_occurrence_envelope (s : State) (i : Site) (f : Field) :
    oldResult s i f = (s.link i f).payload := rfl

theorem original_location_injective (w : LiveTail.WorldId) :
    Function.Injective (fun i => (original w i).ptr.location) := by
  intro i j eq; apply site_code_injective
  have same := congrArg RootLocationId.index eq
  dsimp [original] at same; omega

/-- One tracked parent with exactly three fixed children; no fake field roots. -/
theorem structural_fields_form_one_tree (i : Site) : F1.TreeWellFormed (layout i) := by
  constructor
  · simp [layout]
  · simp [layout]
  · intro p hp q hq same
    simp only [layout,Finset.mem_insert,Finset.mem_singleton] at hp hq
    rcases hp with rfl|rfl|rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl <;>
      cases i <;> simp_all [layout,parentPlace,fieldPlace,Site.code,Field.code]
  · intro p hp ne
    simp only [layout,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl
    · exact False.elim (ne rfl)
    · exact ⟨parentPlace i,by simp [layout],0,by cases i <;> decide⟩
    · exact ⟨parentPlace i,by simp [layout],1,by cases i <;> decide⟩
    · exact ⟨parentPlace i,by simp [layout],2,by cases i <;> decide⟩

/-- Ordinary ptr/Option/byte capabilities compose for the selected H fields.
This does not claim the older TWO-field nominal-completion model checks a
three-link source declaration; that declaration adapter remains unproved. -/
theorem selected_H_field_capabilities (header : Declaration.Header) (cap : Declaration.Capability) :
    (∀ _f : Field, Declaration.Derives header cap 1 (.option (.ptr ⟨0⟩))) ∧
    Declaration.Derives header cap 0 .byte :=
  ⟨fun _ => .option (.ptr ⟨0⟩),.byte⟩

end
end NewLang.Adjunct.FiveRoot
