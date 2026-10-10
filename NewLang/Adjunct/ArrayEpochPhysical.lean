import NewLang.Adjunct.ArrayEpoch

namespace NewLang.Adjunct.ArrayEpoch
open F0 F1.Backing
noncomputable section

/-- One concrete finite geometry. It does not identify numeric addresses with
abstract byte identity in all targets; addresses select this model's layout. -/
def epochBytes (e : Epoch) : Finset AbstractByteId :=
  (Finset.range (size e)).image (fun offset => ⟨e.address+offset⟩)
def elementPlacement (e : Epoch) (i : Nat) : Placement :=
  ⟨region e,(Finset.range 8).image (fun offset => ⟨e.address+32+8*i+offset⟩)⟩
def LiveLocation (e : Epoch) (n : Nat) (l : RootLocationId) : Prop :=
  32*e.generation ≤ l.index ∧ l.index < 32*e.generation+n
instance (e n l) : Decidable (LiveLocation e n l) := inferInstanceAs (Decidable (_ ∧ _))

def physicalFor (e : Epoch) (n : Nat) : PhysicalState where
  world := ⟨{region e},fun _ => epochBytes e,fun _ => ⟨true,true⟩⟩
  placement := fun l => if LiveLocation e n l then
    some (elementPlacement e (l.index-32*e.generation)) else none

private theorem placement_requires_live {e n l pl}
    (placed : (physicalFor e n).placement l = some pl) :
    LiveLocation e n l ∧ pl = elementPlacement e (l.index-32*e.generation) := by
  by_cases h : LiveLocation e n l
  · exact ⟨h,(Option.some.inj (by simpa [physicalFor,h] using placed)).symm⟩
  · simp [physicalFor,h] at placed

/-- The experimental live-prefix partition satisfies the ACCEPTED physical
invariant, including exactness, region extent and pairwise root disjointness.
It does not supply the rich semantic/claim or allocator refinement adapter. -/
theorem epoch_physical_wellFormed (e : Epoch) (n : Nat) (bound : n ≤ e.capacity) :
    PhysicalWellFormed (LiveLocation e n) (physicalFor e n) := by
  constructor
  · intro r hr q hq ne
    have rr : r = region e := by simpa [physicalFor] using hr
    have qq : q = region e := by simpa [physicalFor] using hq
    exact False.elim (ne (rr.trans qq.symm))
  · intro l; constructor
    · intro live
      exact ⟨elementPlacement e (l.index-32*e.generation),by simp [physicalFor,live]⟩
    · rintro ⟨pl,placed⟩; exact (placement_requires_live placed).1
  · intro l pl placed
    rw [(placement_requires_live placed).2]
    simp [physicalFor,elementPlacement]
  · intro l pl placed
    rcases placement_requires_live placed with ⟨live,rfl⟩
    intro byte mem
    rcases Finset.mem_image.mp mem with ⟨offset,off,eq⟩
    subst byte
    apply Finset.mem_image.mpr
    refine ⟨32+8*(l.index-32*e.generation)+offset,?_,?_⟩
    · apply Finset.mem_range.mpr
      have o := Finset.mem_range.mp off
      rcases live with ⟨low,high⟩
      unfold size
      omega
    · congr 1; omega
  · intro l m a b lp mp different
    rcases placement_requires_live lp with ⟨ll,rfl⟩
    rcases placement_requires_live mp with ⟨ml,rfl⟩
    apply Finset.disjoint_left.mpr
    intro byte lb mb
    rcases Finset.mem_image.mp lb with ⟨x,xr,xe⟩
    rcases Finset.mem_image.mp mb with ⟨y,yr,ye⟩
    have eq := congrArg AbstractByteId.index (xe.trans ye.symm)
    have xx := Finset.mem_range.mp xr
    have yy := Finset.mem_range.mp yr
    have ne : l.index ≠ m.index := by
      intro same; exact different (by cases l; cases m; simp_all)
    rcases ll with ⟨ll,lh⟩
    rcases ml with ⟨ml,mh⟩
    simp only at eq
    omega

theorem current_root_has_exact_physical_location {s e p d}
    (current : s.current = some e) (root : CurrentRoot s p d) :
    LiveLocation e s.values.length p.location := by
  rcases root with ⟨a,actual,_,i,bound,rfl⟩
  have eq := Option.some.inj (current.symm.trans actual)
  subst a
  change 32*e.generation ≤ 32*e.generation+i ∧
    32*e.generation+i < 32*e.generation+s.values.length
  omega

theorem grow_has_accepted_physical_post_invariant {s old r} (g : Grow s old r) :
    PhysicalWellFormed (LiveLocation (nextEpoch old r) s.values.length)
      (physicalFor (nextEpoch old r) s.values.length) := by
  have active := (grow_preserves_wellFormed g).active
  have bound : s.values.length ≤ r.capacity := active.2.2.2.2.1
  exact epoch_physical_wellFormed _ _ bound

end
end NewLang.Adjunct.ArrayEpoch
