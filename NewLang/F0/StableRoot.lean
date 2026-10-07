import NewLang.F0.Reference

/-! Issue #27: composition of existing replace, acquisition and lifetime-end proofs.
No new state, pointer representation or transition relation is introduced. -/
namespace NewLang.F0.StableRoot

private theorem acquisition_matches_replace_root
    {cw tc stable access : Prop} {s s' : State} {location : RootLocationId}
    {root : LiveRoot} {incoming : PackageId} {fact : ValueFactId}
    {ptr : PtrToken} {domain : DomainId}
    (before : AcquireRef stable access s ptr domain)
    (replaced : ReplaceStep cw tc s location root incoming fact s')
    (same_site : ptr.location = location) :
    root.incarnation = ptr.incarnation ∧ root.governing = domain := by
  rcases acquire_ref_matches_governing_domain before with ⟨actual, live, inc, dom⟩
  rw [same_site, replaced.2.1.target_live] at live
  have same : root = actual := Occupancy.live.inj live
  simpa [← same] using And.intro inc dom

/-- A pre-replace token keeps the same place/incarnation/domain target while
the current fact changes. This structural statement needs no post access premise. -/
theorem replace_preserves_preexisting_ptr_target
    {cw tc stable access : Prop} {s s' : State} {location : RootLocationId}
    {root : LiveRoot} {incoming : PackageId} {fact : ValueFactId}
    {ptr : PtrToken} {domain : DomainId}
    (before : AcquireRef stable access s ptr domain)
    (replaced : ReplaceStep cw tc s location root incoming fact s')
    (same_site : ptr.location = location) :
    ∃ after, s'.occupancy ptr.location = .live after ∧
      after.place = root.place ∧ after.incarnation = ptr.incarnation ∧
      after.governing = domain ∧ after.currentFact = fact ∧
      after.currentFact ≠ root.currentFact ∧ Governs s' ptr.incarnation domain := by
  rcases acquisition_matches_replace_root before replaced same_site with ⟨inc, dom⟩
  refine ⟨{root with currentFact := fact, package := incoming}, ?_, rfl, inc, dom,
    rfl, replaced.2.1.newFact_ne_old replaced.1, ?_⟩
  · rw [same_site]; exact replaced.2.1.target_after
  · exact ⟨location, _, replaced.2.1.target_after, inc, dom⟩

/-- Reacquisition uses the unchanged token/domain, but still requires the
existing stability and access obligations for the post-state. They may differ
from the propositions discharged before replace. -/
theorem replace_preserves_preexisting_ptr_acquisition
    {cw tc beforeStable beforeAccess afterStable afterAccess : Prop}
    {s s' : State} {location : RootLocationId} {root : LiveRoot}
    {incoming : PackageId} {fact : ValueFactId} {ptr : PtrToken} {domain : DomainId}
    (before : AcquireRef beforeStable beforeAccess s ptr domain)
    (replaced : ReplaceStep cw tc s location root incoming fact s')
    (same_site : ptr.location = location)
    (evidence : afterStable) (allowed : afterAccess) :
    AcquireRef afterStable afterAccess s' ptr domain := by
  rcases acquisition_matches_replace_root before replaced same_site with ⟨inc, dom⟩
  exact ptr_remains_live_across_current_value_replace replaced same_site inc dom evidence allowed

/-- The very token that survives replace becomes unusable when that root's
lifetime subsequently ends. No later access/stability or domain choice revives it. -/
theorem replace_then_take_rejects_preexisting_ptr
    {cw tc ce beforeStable beforeAccess laterStable laterAccess : Prop}
    {s replacedState endedState : State} {location : RootLocationId} {root : LiveRoot}
    {incoming : PackageId} {fact : ValueFactId} {ptr : PtrToken}
    {domain laterDomain : DomainId}
    (before : AcquireRef beforeStable beforeAccess s ptr domain)
    (replaced : ReplaceStep cw tc s location root incoming fact replacedState)
    (same_site : ptr.location = location)
    (ended : TakeStep ce replacedState location
      {root with currentFact := fact, package := incoming} domain endedState) :
    ¬ AcquireRef laterStable laterAccess endedState ptr laterDomain := by
  have inc := (acquisition_matches_replace_root before replaced same_site).1
  exact stale_ptr_after_take_cannot_acquire_ref ended.1 ended.2.1 inc.symm

/-- Destroy has the same stale-token contrast, under its existing discardability
and lifetime-ending legality conditions; replace itself requires neither. -/
theorem replace_then_destroy_rejects_preexisting_ptr
    {cw tc ce beforeStable beforeAccess laterStable laterAccess : Prop}
    {s replacedState endedState : State} {location : RootLocationId} {root : LiveRoot}
    {incoming : PackageId} {fact : ValueFactId} {ptr : PtrToken}
    {domain laterDomain : DomainId}
    (before : AcquireRef beforeStable beforeAccess s ptr domain)
    (replaced : ReplaceStep cw tc s location root incoming fact replacedState)
    (same_site : ptr.location = location)
    (ended : DestroyStep ce replacedState location
      {root with currentFact := fact, package := incoming} domain endedState) :
    ¬ AcquireRef laterStable laterAccess endedState ptr laterDomain := by
  have inc := (acquisition_matches_replace_root before replaced same_site).1
  exact stale_ptr_after_destroy_cannot_acquire_ref ended.1 ended.2.1 inc.symm

end NewLang.F0.StableRoot
