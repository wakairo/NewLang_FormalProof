import NewLang.F1.Backing.Lifetime

namespace NewLang.F1.Occupancy
open F0 Backing
noncomputable section

/-- Region-relative ordinal coordinates, never numeric machine addresses. -/
structure Range where
  base : Nat
  length : Nat
  deriving DecidableEq, Repr

def Range.finish (r : Range) : Nat := r.base + r.length

def Range.positions (r : Range) : Finset Nat :=
  (Finset.range r.finish).filter (fun n => r.base ≤ n)

def Range.left (r : Range) (k : Nat) : Range := ⟨r.base,k⟩
def Range.right (r : Range) (k : Nat) : Range := ⟨r.base+k,r.length-k⟩

def Adjacent (a b : Range) : Prop := a.finish = b.base ∨ b.finish = a.base

def mergeRange (a b : Range) : Range := ⟨min a.base b.base,a.length+b.length⟩

structure Extent where
  region : BackingRegionId
  range : Range
  deriving DecidableEq, Repr

/-- A proof context maps relative coordinates into the reviewed abstract bytes.
Neither coordinates nor this map mint backing identity or authority. -/
structure Geometry where
  capacity : BackingRegionId → Nat
  byteAt : BackingRegionId → Nat → AbstractByteId
  injective : ∀ r, Function.Injective (byteAt r)

def Geometry.Compatible (g : Geometry) (w : World) : Prop :=
  ∀ r, w.bytes r = (Finset.range (g.capacity r)).image (g.byteAt r)

def Extent.footprint (g : Geometry) (e : Extent) : Finset AbstractByteId :=
  e.range.positions.image (g.byteAt e.region)

def Extent.placement (g : Geometry) (e : Extent) : Placement := ⟨e.region,e.footprint g⟩

def Extent.Fits (g : Geometry) (e : Extent) : Prop := e.range.finish ≤ g.capacity e.region

def Extent.left (e : Extent) (k : Nat) : Extent := ⟨e.region,e.range.left k⟩
def Extent.right (e : Extent) (k : Nat) : Extent := ⟨e.region,e.range.right k⟩
def mergeExtent (a b : Extent) : Extent := ⟨a.region,mergeRange a.range b.range⟩

theorem range_membership {r : Range} {n : Nat} :
    n ∈ r.positions ↔ r.base ≤ n ∧ n < r.finish := by
  simp [Range.positions,and_comm]

theorem nonempty_range_has_position {r : Range} (positive : 0 < r.length) :
    r.base ∈ r.positions := by rw [range_membership]; simp [Range.finish,positive]

theorem split_ranges_are_nonempty {r : Range} {k : Nat} (low : 0 < k) (high : k < r.length) :
    0 < (r.left k).length ∧ 0 < (r.right k).length := by
  simp only [Range.left,Range.right]; omega

theorem split_ranges_exact_union {r : Range} {k : Nat} (high : k ≤ r.length) :
    (r.left k).positions ∪ (r.right k).positions = r.positions := by
  ext n; simp only [Finset.mem_union,range_membership,Range.left,Range.right,Range.finish]
  omega

theorem split_ranges_disjoint (r : Range) (k : Nat) :
    Disjoint (r.left k).positions (r.right k).positions := by
  apply Finset.disjoint_left.mpr
  intro n left right
  simp only [range_membership,Range.left,Range.right,Range.finish] at left right
  omega

theorem split_extents_preserve_region (e : Extent) (k : Nat) :
    (e.left k).region = e.region ∧ (e.right k).region = e.region := ⟨rfl,rfl⟩

theorem split_extents_exact_union (g : Geometry) {e : Extent} {k : Nat} (high : k ≤ e.range.length) :
    (e.left k).footprint g ∪ (e.right k).footprint g = e.footprint g := by
  change ((e.range.left k).positions.image (g.byteAt e.region)) ∪
    ((e.range.right k).positions.image (g.byteAt e.region)) = _
  rw [← Finset.image_union,split_ranges_exact_union high]; rfl

theorem split_extents_disjoint (g : Geometry) (e : Extent) (k : Nat) :
    Disjoint ((e.left k).footprint g) ((e.right k).footprint g) :=
  (Finset.disjoint_image (g.injective e.region)).mpr (split_ranges_disjoint e.range k)

theorem adjacent_ranges_disjoint {a b : Range} (adjacent : Adjacent a b) :
    Disjoint a.positions b.positions := by
  apply Finset.disjoint_left.mpr
  intro n left right
  simp only [range_membership] at left right
  rcases adjacent with forward | backward <;> omega

theorem adjacent_ranges_exact_union {a b : Range} (ap : 0 < a.length) (bp : 0 < b.length)
    (adjacent : Adjacent a b) : a.positions ∪ b.positions = (mergeRange a b).positions := by
  rcases adjacent with forward | backward
  · have order : a.base ≤ b.base := by simp only [Range.finish] at forward; omega
    ext n
    simp only [Finset.mem_union,range_membership,mergeRange,Nat.min_eq_left order,Range.finish]
    simp only [Range.finish] at forward; omega
  · have order : b.base ≤ a.base := by simp only [Range.finish] at backward; omega
    ext n
    simp only [Finset.mem_union,range_membership,mergeRange,Nat.min_eq_right order,Range.finish]
    simp only [Range.finish] at backward; omega

theorem adjacent_extents_exact_union (g : Geometry) {a b : Extent}
    (same : a.region = b.region) (ap : 0 < a.range.length) (bp : 0 < b.range.length)
    (adjacent : Adjacent a.range b.range) :
    a.footprint g ∪ b.footprint g = (mergeExtent a b).footprint g := by
  simp only [Extent.footprint,mergeExtent,← same]
  rw [← Finset.image_union,adjacent_ranges_exact_union ap bp adjacent]

theorem adjacent_extents_disjoint (g : Geometry) {a b : Extent}
    (same : a.region = b.region) (adjacent : Adjacent a.range b.range) :
    Disjoint (a.footprint g) (b.footprint g) := by
  simp only [Extent.footprint,← same]
  exact (Finset.disjoint_image (g.injective a.region)).mpr (adjacent_ranges_disjoint adjacent)

theorem split_merge_range_roundtrip {r : Range} {k : Nat} (low : 0 < k) (high : k < r.length) :
    mergeRange (r.left k) (r.right k) = r := by
  cases r with
  | mk base length =>
    dsimp only at high
    have order : base ≤ base+k := by omega
    simp only [mergeRange,Range.left,Range.right,Nat.min_eq_left order,Range.mk.injEq]
    exact ⟨trivial,by omega⟩

theorem extent_footprint_nonempty (g : Geometry) {e : Extent} (positive : 0 < e.range.length) :
    (e.footprint g).Nonempty :=
  ⟨g.byteAt e.region e.range.base,Finset.mem_image.mpr ⟨_,nonempty_range_has_position positive,rfl⟩⟩

theorem fitting_extent_is_inside_backing {g : Geometry} {w : World} (compatible : g.Compatible w)
    {e : Extent} (fits : e.Fits g) : e.footprint g ⊆ w.bytes e.region := by
  rw [compatible e.region]
  intro byte member
  rcases Finset.mem_image.mp member with ⟨n,position,rfl⟩
  refine Finset.mem_image.mpr ⟨n,Finset.mem_range.mpr ?_,rfl⟩
  have bounds := range_membership.mp position
  exact lt_of_lt_of_le bounds.2 fits

end
end NewLang.F1.Occupancy
