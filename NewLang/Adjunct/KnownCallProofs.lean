import NewLang.Adjunct.KnownCall

namespace NewLang.Adjunct.KnownCall
open F0 F1.Backing F1.Occupancy
noncomputable section

/-- Copying a locator leaves every authority and memory component unchanged. -/
def copyPtr (s : State) (ptr : AccessPtr) : State × AccessPtr × AccessPtr := (s, ptr, ptr)

theorem copy_ptr_grants_no_authority (s : State) (ptr : AccessPtr) :
    (copyPtr s ptr).1 = s := rfl

theorem transfer_preserves_memory (s : State) (a d : F2.BindingId) :
    (transfer s a d).head = s.head ∧ (transfer s a d).tail = s.tail ∧
    (transfer s a d).externalDependencies = s.externalDependencies ∧
    (transfer s a d).blockers = s.blockers := ⟨rfl,rfl,rfl,rfl⟩

theorem transfer_preserves_exact_responsibility (c : Context) (s : State) (a d : F2.BindingId) (i : Site) :
    responsibility c (transfer s a d) i = responsibility c s i := by cases i <;> rfl

theorem transfer_records_fresh_parameters {s : State} {a d : F2.BindingId}
    (fresh : FreshParameters s a d) :
    a ≠ d ∧ a ∉ s.usedBindings ∧ d ∉ s.usedBindings ∧
    a ∈ (transfer s a d).usedBindings ∧ d ∈ (transfer s a d).usedBindings ∧
    s.usedBindings ⊆ (transfer s a d).usedBindings := by
  refine ⟨fresh.distinct,fresh.allocationFresh,fresh.domainFresh,by simp [transfer],by simp [transfer],?_⟩
  intro b member; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)

theorem transfer_consumes_donor {c : Context} {s : State} {args : Arguments} {a d : F2.BindingId}
    (wf : WellFormed c s) (entry : RequiredAtEntry c s args) (fresh : FreshParameters s a d) :
    (transfer s a d).carrier .tailAllocation = some a ∧
    (transfer s a d).carrier .tailDomain = some d ∧
    (∀ r, (transfer s a d).carrier r ≠ some args.allocationBinding) ∧
    (∀ r, (transfer s a d).carrier r ≠ some args.domainBinding) := by
  have fa : a ≠ args.allocationBinding := by
    intro eq; exact fresh.allocationFresh (eq ▸ wf.recorded _ _ entry.allocation)
  have fd : d ≠ args.allocationBinding := by
    intro eq; exact fresh.domainFresh (eq ▸ wf.recorded _ _ entry.allocation)
  have ga : a ≠ args.domainBinding := by
    intro eq; exact fresh.allocationFresh (eq ▸ wf.recorded _ _ entry.domain)
  have gd : d ≠ args.domainBinding := by
    intro eq; exact fresh.domainFresh (eq ▸ wf.recorded _ _ entry.domain)
  refine ⟨rfl,rfl,?_,?_⟩
  · intro r same; cases r with
    | headAllocation => have bad := wf.unique _ _ _ same entry.allocation; cases bad
    | headDomain => have bad := wf.unique _ _ _ same entry.allocation; cases bad
    | tailAllocation => exact fa (Option.some.inj same)
    | tailDomain => exact fd (Option.some.inj same)
  · intro r same; cases r with
    | headAllocation => have bad := wf.unique _ _ _ same entry.domain; cases bad
    | headDomain => have bad := wf.unique _ _ _ same entry.domain; cases bad
    | tailAllocation => exact ga (Option.some.inj same)
    | tailDomain => exact gd (Option.some.inj same)

theorem transfer_preserves_wellFormed {c : Context} {s : State} {args : Arguments} {a d : F2.BindingId}
    (wf : WellFormed c s) (entry : RequiredAtEntry c s args) (fresh : FreshParameters s a d) :
    WellFormed c (transfer s a d) := by
  constructor
  · intro i; cases i with
    | head => exact wf.allocation .head
    | tail => simp [transfer,allocationRole,State.cell,entry.live]
  · intro i; cases i with
    | head => exact wf.domain .head
    | tail => simpa [transfer,domainRole,State.cell] using wf.typedDomain .tail entry.live
  · exact wf.typedDomain
  · exact wf.slotDomain
  · exact wf.releasedDomain
  · exact wf.releaseCount
  · intro r b present; cases r with
    | headAllocation => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.recorded _ _ present))
    | headDomain => exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (wf.recorded _ _ present))
    | tailAllocation => have eq := Option.some.inj present; subst b; simp [transfer]
    | tailDomain => have eq := Option.some.inj present; subst b; simp [transfer]
  · intro r q b rb qb
    have oldA : ∀ r, s.carrier r ≠ some a := by
      intro r present; exact fresh.allocationFresh (wf.recorded r a present)
    have oldD : ∀ r, s.carrier r ≠ some d := by
      intro r present; exact fresh.domainFresh (wf.recorded r d present)
    cases r <;> cases q <;>
      simp only [transfer] at rb qb <;>
      first | rfl | exact wf.unique _ _ _ rb qb |
        (have eq := Option.some.inj rb; subst b; exact False.elim (oldA _ qb)) |
        (have eq := Option.some.inj qb; subst b; exact False.elim (oldA _ rb)) |
        (have eq := Option.some.inj rb; subst b; exact False.elim (oldD _ qb)) |
        (have eq := Option.some.inj qb; subst b; exact False.elim (oldD _ rb)) |
        exact False.elim (fresh.distinct ((Option.some.inj rb).trans (Option.some.inj qb).symm)) |
        exact False.elim (fresh.distinct ((Option.some.inj qb).trans (Option.some.inj rb).symm))
  · exact wf.dependencies

/-- Definition-time relative body effect, independent of any favorable caller. -/
theorem receiver_effect (s : State) :
    (receiver s).head = s.head ∧
    (receiver s).tail.phase = .released ∧ (receiver s).tail.domainLive = false ∧
    (receiver s).tail.releases = s.tail.releases + 1 ∧
    (receiver s).carrier .tailAllocation = none ∧ (receiver s).carrier .tailDomain = none ∧
    (receiver s).carrier .headAllocation = s.carrier .headAllocation ∧
    (receiver s).carrier .headDomain = s.carrier .headDomain := by
  simp [receiver,endRoot,eraseSlot,finalize,deallocate]

theorem strict_recovery_order (c : Context) (s : State) :
    responsibility c (endRoot s) .tail = some (.slot c.type c.tail.extent) ∧
    responsibility c (eraseSlot (endRoot s)) .tail = some (.storage c.tail.extent) ∧
    responsibility c (finalize (eraseSlot (endRoot s))) .tail = some (.storage c.tail.extent) ∧
    responsibility c (receiver s) .tail = none := by
  simp [responsibility,Context.root,State.cell,endRoot,eraseSlot,finalize,receiver,deallocate]

/-- The original full-R extent is recovered, not the caller argument's guessed region. -/
theorem recovery_is_original_full_range {g c} (valid : ContextValid g c) (s : State) :
    responsibility c (finalize (eraseSlot (endRoot s))) .tail = some (.storage c.tail.extent) ∧
    c.tail.extent.range = ⟨0,g.capacity c.tail.extent.region⟩ ∧ 0 < c.tail.extent.range.length := by
  refine ⟨(strict_recovery_order c s).2.2.1,valid.full .tail,?_⟩
  change 0 < (c.root .tail).extent.range.length
  rw [valid.exactSize .tail]; exact valid.nonempty

/-- Exact ended facts are rejected; surviving dependency data is unchanged. -/
theorem receiver_dependencies_valid {c : Context} {s : State}
    (wf : WellFormed c s) (guard : SurvivorGuard c s) : DependenciesValid c (receiver s) := by
  have retained : ∀ f, (f ∈ c.head.dependencies ∨ f ∈ s.externalDependencies) →
      FactLive c s f → FactLive c (receiver s) f := by
    intro f member live
    cases f with
    | valueFact p vf =>
      rcases live with ⟨i,typed,place,fact⟩
      cases i with
      | head => exact ⟨.head,typed,place,fact⟩
      | tail => exact False.elim ((guard _ member).1 (by simp [Context.root] at place fact; subst p; subst vf; rfl))
    | domainLive d =>
      rcases live with ⟨i,dl,identity⟩
      cases i with
      | head => exact ⟨.head,dl,identity⟩
      | tail => exact False.elim ((guard _ member).2 (by simp [Context.root] at identity; subst d; rfl))
  constructor
  · intro i typed f dep
    cases i with
    | head => exact retained f (Or.inl dep) (wf.dependencies.1 .head typed f dep)
    | tail => simp [State.cell,receiver,deallocate] at typed
  · intro f dep
    exact retained f (Or.inr dep) (wf.dependencies.2 f dep)

/-- Substantive preservation: post invariant is derived, not a step premise. -/
theorem receiver_preserves_wellFormed {c : Context} {s : State} {args : Arguments}
    (wf : WellFormed c s) (entry : RequiredAtEntry c s args) (guard : SurvivorGuard c s) :
    WellFormed c (receiver s) := by
  have zero : s.tail.releases = 0 := by
    have count := wf.releaseCount .tail
    simpa [State.cell,entry.live] using count
  constructor
  · intro i; cases i with
    | head => simpa [receiver,deallocate,finalize,eraseSlot,endRoot,allocationRole,State.cell] using wf.allocation .head
    | tail => simp [receiver,deallocate,allocationRole,State.cell]
  · intro i; cases i with
    | head => simpa [receiver,deallocate,finalize,eraseSlot,endRoot,domainRole,State.cell] using wf.domain .head
    | tail => simp [receiver,deallocate,finalize,domainRole,State.cell]
  · intro i; cases i with
    | head => exact wf.typedDomain .head
    | tail => simp [receiver,deallocate,State.cell]
  · intro i; cases i with
    | head => exact wf.slotDomain .head
    | tail => simp [receiver,deallocate,State.cell]
  · intro i; cases i with
    | head => exact wf.releasedDomain .head
    | tail => simp [receiver,deallocate,finalize,State.cell]
  · intro i; cases i with
    | head => exact wf.releaseCount .head
    | tail => simp [receiver,deallocate,finalize,eraseSlot,endRoot,State.cell,zero]
  · intro r b present
    cases r <;> simp [receiver,deallocate,finalize] at present
    · exact wf.recorded _ _ present
    · exact wf.recorded _ _ present
  · intro r q b rb qb
    cases r <;> cases q <;> simp [receiver,deallocate,finalize] at rb qb
    all_goals exact wf.unique _ _ _ rb qb
  · exact receiver_dependencies_valid wf guard

theorem transferred_entry {c s args a d} (entry : RequiredAtEntry c s args)
    (fresh : FreshParameters s a d) :
    RequiredAtEntry c (transfer s a d)
      {args with allocationBinding := a, domainBinding := d} := by
  exact ⟨entry.headLive,entry.live,entry.ptrRoot,entry.ptrRegion,entry.read,entry.issued,entry.access,entry.allocationRegion,rfl,
    entry.domainIdentity,rfl,fresh.allocationScope,fresh.domainScope,entry.rootScope,entry.domainScope,
    entry.regionScope,entry.discardable,entry.platform⟩

theorem known_call_preserves_wellFormed {g c s args a d post}
    (call : Call g c s args a d post) : WellFormed c post := by
  rcases call with ⟨_,wf,entry,fresh,guard,rfl⟩
  exact receiver_preserves_wellFormed (transfer_preserves_wellFormed wf entry fresh)
    (transferred_entry entry fresh) guard

theorem call_ends_only_original_tail {g c s args a d post}
    (call : Call g c s args a d post) :
    post.head = s.head ∧ post.head.phase = .typed ∧ post.tail.phase = .released ∧
    post.tail.domainLive = false ∧ post.tail.releases = 1 ∧
    post.carrier .tailAllocation = none ∧ post.carrier .tailDomain = none := by
  rcases call with ⟨_,wf,entry,_,_,rfl⟩
  have zero : s.tail.releases = 0 := by simpa [State.cell,entry.live] using wf.releaseCount .tail
  simp [callPost,receiver,transfer,endRoot,eraseSlot,finalize,deallocate,zero,entry.headLive]

theorem known_call_cannot_double_release {g c s args a d post}
    (call : Call g c s args a d post) (b : F2.BindingId) (raw : Extent) :
    ¬ CanDeallocate c post b raw := by
  intro next
  have ended := (call_ends_only_original_tail call).2.2.1
  have phase := next.1
  rw [ended] at phase
  cases phase

theorem known_call_preserves_head_authorities {g c s args a d post}
    (call : Call g c s args a d post) :
    post.carrier .headAllocation = s.carrier .headAllocation ∧
    post.carrier .headDomain = s.carrier .headDomain := by
  rw [call.2.2.2.2.2]
  simp [callPost,receiver,transfer,endRoot,eraseSlot,finalize,deallocate]

theorem matched_receiver_can_deallocate {c s args a d}
    (wf : WellFormed c s) (entry : RequiredAtEntry c s args) :
    CanDeallocate c (finalize (eraseSlot (endRoot (transfer s a d)))) a c.tail.extent := by
  have zero : s.tail.releases = 0 := by simpa [State.cell,entry.live] using wf.releaseCount .tail
  simp [CanDeallocate,transfer,endRoot,eraseSlot,finalize,entry.platform,entry.regionScope,zero]

theorem release_rejects_nonfull_or_other_region {c s a raw}
    (wrong : raw ≠ c.tail.extent) : ¬ CanDeallocate c s a raw :=
  fun h => wrong h.2.2.2.1

theorem typed_root_cannot_release {c s a raw} (live : s.tail.phase = .typed) :
    ¬ CanDeallocate c s a raw := by intro h; have phase := h.1; rw [live] at phase; cases phase

theorem entry_rejects_wrong_ptr {c s args}
    (wrong : args.ptr.token ≠ ⟨c.tail.location,c.tail.incarnation⟩) : ¬ RequiredAtEntry c s args :=
  fun h => wrong h.ptrRoot

theorem entry_rejects_wrong_allocation_region {c s args}
    (wrong : args.allocationRegion ≠ c.tail.extent.region) : ¬ RequiredAtEntry c s args :=
  fun h => wrong h.allocationRegion

theorem entry_rejects_wrong_domain {c s args}
    (wrong : args.domain ≠ c.tail.domain) : ¬ RequiredAtEntry c s args :=
  fun h => wrong h.domainIdentity

theorem entry_rejects_absent_donor {c s args}
    (missing : s.carrier .tailAllocation = none) : ¬ RequiredAtEntry c s args := by
  intro h; have carrier := h.allocation; rw [missing] at carrier; cases carrier

theorem entry_rejects_scope_conflict {c s args}
    (blocked : .root c.tail.incarnation ∈ s.blockers) : ¬ RequiredAtEntry c s args :=
  fun h => h.rootScope blocked


theorem transfer_preserves_governing_and_locator (c : Context) (s : State) (a d : F2.BindingId)
    (o : IncarnationId) (domain : DomainId) (ptr : PtrToken) :
    (Governs c (transfer s a d) o domain ↔ Governs c s o domain) ∧
    (CurrentLocator c (transfer s a d) ptr ↔ CurrentLocator c s ptr) := by
  constructor <;> simp only [Governs,CurrentLocator]
  all_goals constructor <;> rintro ⟨i,live,rest⟩ <;> exact ⟨i,by cases i <;> exact live,rest⟩

theorem matched_receiver_primitive_applicability {g c s args a d}
    (valid : ContextValid g c) (wf : WellFormed c s) (entry : RequiredAtEntry c s args)
    (guard : SurvivorGuard c s) :
    CanEnd c (transfer s a d) d ∧ CanEraseSlot (endRoot (transfer s a d)) ∧
    CanFinalize c (eraseSlot (endRoot (transfer s a d))) d ∧
    CanDeallocate c (finalize (eraseSlot (endRoot (transfer s a d)))) a c.tail.extent := by
  refine ⟨?_,rfl,?_,matched_receiver_can_deallocate wf entry⟩
  · exact ⟨entry.live,rfl,entry.rootScope,entry.discardable⟩
  · refine ⟨rfl,wf.typedDomain .tail entry.live,rfl,entry.domainScope,?_,?_⟩
    · rintro o ⟨i,live,inc,dom⟩
      cases i with
      | head => exact valid.domains dom
      | tail => simp [State.cell,eraseSlot] at live
    · intro f member; exact (guard f member).2

theorem matched_transfer_keeps_original_root {c s args a d} (entry : RequiredAtEntry c s args) :
    Governs c (transfer s a d) c.tail.incarnation c.tail.domain ∧
    CurrentLocator c (transfer s a d) args.ptr.token := by
  exact ⟨⟨.tail,entry.live,rfl,rfl⟩,⟨.tail,entry.live,entry.ptrRoot⟩⟩

theorem ended_tail_fact_and_domain_not_live {g c s}
    (valid : ContextValid g c) :
    ¬ FactLive c (receiver s) (.valueFact c.tail.place c.tail.currentFact) ∧
    ¬ FactLive c (receiver s) (.domainLive c.tail.domain) := by
  constructor
  · rintro ⟨i,live,place,fact⟩
    cases i with
    | head => exact valid.places place
    | tail => simp [State.cell,receiver,deallocate] at live
  · rintro ⟨i,live,domain⟩
    cases i with
    | head => exact valid.domains domain
    | tail => simp [State.cell,receiver,deallocate,finalize] at live

theorem ended_tail_ptr_cannot_reacquire {g c s}
    (valid : ContextValid g c) : ¬ CurrentLocator c (receiver s) ⟨c.tail.location,c.tail.incarnation⟩ := by
  rintro ⟨i,live,token⟩
  cases i with
  | head => exact valid.locations (congrArg PtrToken.location token).symm
  | tail => simp [State.cell,receiver,deallocate] at live

theorem rejected_entry_has_no_call {g c s args a d post}
    (rejected : ¬ RequiredAtEntry c s args) : ¬ Call g c s args a d post :=
  fun h => rejected h.2.2.1

theorem surviving_ended_dependency_has_no_call {g c s args a d post}
    (rejected : ¬ SurvivorGuard c s) : ¬ Call g c s args a d post :=
  fun h => rejected h.2.2.2.2.1

theorem parameter_bindings_are_consumed_at_return {g c s args a d post}
    (call : Call g c s args a d post) :
    ∀ r, post.carrier r ≠ some a ∧ post.carrier r ≠ some d := by
  intro r
  rcases call with ⟨_,wf,_,fresh,_,rfl⟩
  have oldA : ∀ r, s.carrier r ≠ some a := fun r present => fresh.allocationFresh (wf.recorded r a present)
  have oldD : ∀ r, s.carrier r ≠ some d := fun r present => fresh.domainFresh (wf.recorded r d present)
  cases r <;> simp [callPost,receiver,transfer,deallocate,finalize]
  all_goals exact ⟨oldA _,oldD _⟩

/-- Finite accounting view of the single responsibility for each original region. -/
def responsibleBytes (g : Geometry) (c : Context) (s : State) (i : Site) : Finset AbstractByteId :=
  ((responsibility c s i).map (fun claim => claim.extent.footprint g)).getD ∅

theorem call_conserves_exact_region_responsibility {g c s args a d post}
    (call : Call g c s args a d post) :
    responsibility c post .head = responsibility c s .head ∧
    responsibility c post .tail = none ∧
    responsibleBytes g c s .head ∪ responsibleBytes g c s .tail =
      responsibleBytes g c post .head ∪ c.tail.extent.footprint g ∧
    Disjoint (responsibleBytes g c post .head) (c.tail.extent.footprint g) := by
  rcases call with ⟨valid,_,entry,_,_,rfl⟩
  simp only [responsibleBytes,responsibility,State.cell,callPost,receiver,transfer,deallocate,finalize,
    eraseSlot,endRoot,Context.root,entry.headLive,entry.live,Claim.extent,Option.map_some,Option.getD_some]
  exact ⟨trivial,trivial,trivial,valid.disjoint⟩

theorem call_preserves_dependency_data {g c s args a d post}
    (call : Call g c s args a d post) : post.externalDependencies = s.externalDependencies ∧
    post.issuedPtrs = s.issuedPtrs ∧ post.usedBindings = insert a (insert d s.usedBindings) := by
  rw [call.2.2.2.2.2]; exact ⟨rfl,rfl,rfl⟩

end
end NewLang.Adjunct.KnownCall
