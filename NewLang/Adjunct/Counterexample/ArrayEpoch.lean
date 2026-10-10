import NewLang.Adjunct.ArrayEpochPhysical

namespace NewLang.Adjunct.ArrayEpoch.Counterexample
open F0 F1.Backing
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def d : DomainId := ⟨7⟩
def package (i : Nat) : Package := ⟨⟨i⟩,17*i+3⟩
def packages (n : Nat) := (List.range n).map package

def e4 : Epoch := ⟨1,1000,4,d⟩
def to8 : Request := ⟨2,1000,8⟩
def to16 : Request := ⟨3,1000,16⟩
def move8 : Request := ⟨2,2000,8⟩
def move16 : Request := ⟨3,3000,16⟩

def pre4 : State where
  current := some e4
  ownerCredits := [1]
  values := packages 4
  returned := []
  len := 4
  cap := 4
  used := {1}
  releases := []
  loans := ∅
  endingDomains := {d}

theorem pre4_wellFormed : WellFormed pre4 := by
  constructor
  · decide
  · decide
  · decide
  · intro g mem; simp [pre4] at mem

theorem grow4_to8 : Grow pre4 e4 to8 := by
  exact ⟨pre4_wellFormed,rfl,rfl,by decide,by decide,by decide,by decide⟩

def after8 := candidate pre4 e4 to8

theorem after8_wellFormed : WellFormed after8 := grow_preserves_wellFormed grow4_to8

/-- Four new incoming scalar packages, in a separately reconstructed finite
initialized state. This is NOT a proof of four source-level push operations. -/
def full8 : State := {after8 with values := packages 8,len := 8}

theorem full8_wellFormed : WellFormed full8 := by
  constructor
  · decide
  · decide
  · decide
  · intro g mem
    have eq : g = 1 := by simpa [full8,after8,candidate,pre4,e4] using mem
    subst g; decide

theorem grow8_to16 : Grow full8 (nextEpoch e4 to8) to16 := by
  exact ⟨full8_wellFormed,rfl,rfl,by decide,by decide,by decide,by decide⟩

def after16 := candidate full8 (nextEpoch e4 to8) to16

theorem after16_wellFormed : WellFormed after16 := grow_preserves_wellFormed grow8_to16

theorem same_numeric_address_two_fresh_epochs :
    (nextEpoch e4 to8).address = e4.address ∧
    (nextEpoch (nextEpoch e4 to8) to16).address = e4.address ∧
    region e4 ≠ region (nextEpoch e4 to8) ∧
    region (nextEpoch e4 to8) ≠ region (nextEpoch (nextEpoch e4 to8) to16) ∧
    after16.ownerCredits = [3] ∧ after16.releases = [2,1] := by decide

theorem same_address_element_incarnations_fresh (i : Nat) (hi : i < 4) :
    incarnation (nextEpoch e4 to8) i ≠ incarnation e4 i ∧
    incarnation (nextEpoch e4 to8) i ∉ historicalIncarnations pre4 :=
  ⟨fresh_elements_have_new_incarnations grow4_to8 i i (by simpa [pre4,packages] using hi) (by omega),
    new_incarnation_not_historically_allocated grow4_to8 i (by omega)⟩

theorem all_eight_incarnations_regenerated (i : Nat) (hi : i < 8) :
    incarnation (nextEpoch (nextEpoch e4 to8) to16) i ≠ incarnation (nextEpoch e4 to8) i :=
  fresh_elements_have_new_incarnations grow8_to16 i i
    (by simpa [full8,packages] using hi) (by omega)

theorem force_move4_to8 : Grow pre4 e4 move8 := by
  exact ⟨pre4_wellFormed,rfl,rfl,by decide,by decide,by decide,by decide⟩

def forceAfter8 := candidate pre4 e4 move8
def forceFull8 := {forceAfter8 with values := packages 8,len := 8}

theorem forceFull8_wellFormed : WellFormed forceFull8 := by
  constructor
  · decide
  · decide
  · decide
  · intro g mem
    have eq : g = 1 := by simpa [forceFull8,forceAfter8,candidate,pre4,e4] using mem
    subst g; decide

theorem force_move8_to16 : Grow forceFull8 (nextEpoch e4 move8) move16 := by
  exact ⟨forceFull8_wellFormed,rfl,rfl,by decide,by decide,by decide,by decide⟩

theorem two_forced_moves_preserve_affine_values :
    (candidate pre4 e4 move8).values = pre4.values ∧
    (candidate forceFull8 (nextEpoch e4 move8) move16).values = forceFull8.values ∧
    (nextEpoch e4 move8).address ≠ e4.address ∧
    (nextEpoch (nextEpoch e4 move8) move16).address ≠ (nextEpoch e4 move8).address :=
  ⟨rfl,rfl,by decide,by decide⟩

def empty4 := {pre4 with values := [],len := 0}

theorem empty4_wellFormed : WellFormed empty4 := by
  constructor
  · decide
  · decide
  · decide
  · intro g mem; simp [empty4,pre4] at mem

theorem empty_grow_has_no_fabricated_element :
    Grow empty4 e4 to8 ∧ (candidate empty4 e4 to8).values = [] :=
  ⟨⟨empty4_wellFormed,rfl,rfl,by decide,by decide,by decide,by decide⟩,rfl⟩

theorem failed_grow_keeps_all_old_authority_and_handles :
    execute pre4 e4 to8 .failure = pre4 ∧
    CurrentRoot (execute pre4 e4 to8 .failure) (token e4 0) d :=
  ⟨rfl,e4,rfl,rfl,0,by decide,rfl⟩

theorem old_ptr_same_address_rejected : ¬ CurrentRoot after8 (token e4 0) d :=
  old_ptr_cannot_be_reacquired grow4_to8 0 (by decide)

theorem fresh_ptr_same_address_is_current :
    CurrentRoot after8 (token (nextEpoch e4 to8) 0) d :=
  fresh_root_is_current grow4_to8 0 (by decide)

def borrowed := {pre4 with loans := {d}}

theorem active_span_blocks_ending_even_with_domain_authority :
    CurrentSpan borrowed e4 4 ∧ d ∈ borrowed.endingDomains ∧ ¬ Grow borrowed e4 to8 :=
  ⟨⟨rfl,by decide,by decide⟩,by decide,span_blocks_grow (by decide)⟩

theorem new_current_span_has_valid_epoch_and_live_count :
    CurrentSpan {after8 with loans := {d}} (nextEpoch e4 to8) 4 :=
  ⟨rfl,by decide,by decide⟩

def wrongDomain := {pre4 with endingDomains := {(⟨8⟩ : DomainId)}}

theorem wrong_domain_does_not_authorize_growth : ¬ Grow wrongDomain e4 to8 := by
  intro g; have h := g.ending; change d ∈ ({⟨8⟩} : Finset DomainId) at h
  have no : d ∉ ({⟨8⟩} : Finset DomainId) := by decide
  exact no h

def forgedMetadata := {pre4 with len := 5}

theorem out_of_bounds_metadata_mints_neither_root_nor_span :
    forgedMetadata.len ≤ forgedMetadata.cap + 1 ∧
    ¬ CurrentRoot forgedMetadata (token e4 4) d ∧
    ¬ CurrentSpan {forgedMetadata with loans := {d}} e4 5 := by
  refine ⟨by decide,?_,?_⟩
  · rintro ⟨e,eq,_,i,bound,same⟩
    have ee : e = e4 := (Option.some.inj eq).symm
    subst e
    have ii := congrArg (fun p : PtrToken => p.incarnation.index) same
    simp [token,incarnation] at ii
    have bl : i < 4 := by simpa [forgedMetadata,pre4,packages] using bound
    omega
  · intro h; have impossible := h.2.1
    have no : ¬ 5 ≤ (packages 4).length := by decide
    exact no impossible

/-- All numeric len/cap bounds hold, but the actual live list has only four roots. -/
def plausibleFake := {after8 with len := 5}

theorem plausible_metadata_is_not_an_invariant :
    plausibleFake.len ≤ plausibleFake.cap ∧ ¬ WellFormed plausibleFake := by
  refine ⟨by decide,?_⟩
  intro wf
  have h := wf.active
  have eq : plausibleFake.len = plausibleFake.values.length := h.2.2.1
  have no : plausibleFake.len ≠ plausibleFake.values.length := by decide
  exact no eq

/-- A two-region ordinary-safe prestate over the SAME abstract byte instances. -/
def aliasWorld : World where
  liveRegions := {region e4,region (nextEpoch e4 to8)}
  bytes := fun _ => {⟨0⟩}
  access := fun _ => ⟨true,true⟩

theorem aliasing_old_new_regions_rejected_by_existing_kernel : ¬ RegionsDisjoint aliasWorld := by
  apply aliasing_live_epochs_are_not_safe (a := region e4) (b := region (nextEpoch e4 to8))
  · decide
  · decide
  · decide
  · decide

/-- Full 64/96-byte disjoint force branch; abstract byte labels here implement a
chosen faithful finite geometry, not a universal numeric-address assumption. -/
def fullBytes (e : Epoch) : Finset AbstractByteId :=
  (Finset.range (size e)).image (fun offset => ⟨e.address+offset⟩)
def forceWorld : World where
  liveRegions := {region e4,region (nextEpoch e4 move8)}
  bytes := fun r => if r = region e4 then fullBytes e4 else fullBytes (nextEpoch e4 move8)
  access := fun _ => ⟨true,true⟩

theorem force_allocate_before_end_is_disjoint : RegionsDisjoint forceWorld := by
  intro r hr q hq ne
  have rs : r = region e4 ∨ r = region (nextEpoch e4 move8) := by simpa [forceWorld] using hr
  have qs : q = region e4 ∨ q = region (nextEpoch e4 move8) := by simpa [forceWorld] using hq
  rcases rs with rfl|rfl <;> rcases qs with rfl|rfl
  · exact False.elim (ne rfl)
  · decide
  · decide
  · exact False.elim (ne rfl)

theorem successful_same_address_is_not_same_place :
    region e4 ≠ region (nextEpoch e4 to8) ∧ size e4 ≠ size (nextEpoch e4 to8) := by decide

def lostAfterSuccess := {after8 with ownerCredits := []}
def droppedOnFailure := {pre4 with ownerCredits := []}

theorem successful_owner_loss_rejected : ¬ WellFormed lostAfterSuccess := by
  intro wf; have eq := wf.active.1
  have ne : lostAfterSuccess.ownerCredits ≠ [(nextEpoch e4 to8).generation] := by decide
  exact ne eq

theorem failed_grow_owner_drop_rejected : ¬ WellFormed droppedOnFailure := by
  intro wf; have eq := wf.active.1
  have ne : droppedOnFailure.ownerCredits ≠ [e4.generation] := by decide
  exact ne eq

/-- A live nonCopy token raw-copied to a second root has valid metadata/size but
fails affine uniqueness. Actual raw byte copy is NOT such a semantic transition. -/
def duplicatedPayload := {after8 with values := (packages 4) ++ [package 0],len := 5}

theorem raw_copy_laundering_breaks_only_affine_uniqueness :
    ActiveInvariant duplicatedPayload ∧ ¬ WellFormed duplicatedPayload := by
  refine ⟨by decide,?_⟩
  intro wf
  have no : ¬ ((duplicatedPayload.values ++ duplicatedPayload.returned).map Package.id).Nodup := by decide
  exact no wf.uniqueValues

theorem header_base_and_sizes_match_observed_fixture :
    size e4 = 64 ∧ size (nextEpoch e4 to8) = 96 ∧
    size (nextEpoch (nextEpoch e4 to8) to16) = 160 := by decide

/-- Transfers eight current affine values to EXPLICIT result custody before free;
it does not discard them and does not prove stb's delete/pop suffix. -/
def taken := takeAll after16

theorem taken_wellFormed : WellFormed taken := take_all_transports_without_discard after16_wellFormed

theorem final_current_owner_free : FreeAt taken (nextEpoch (nextEpoch e4 to8) to16) 1000 :=
  ⟨⟨taken_wellFormed,rfl,rfl,rfl⟩,rfl⟩

def freed := freeCandidate taken (nextEpoch (nextEpoch e4 to8) to16)

theorem freed_wellFormed : WellFormed freed := free_preserves_wellFormed final_current_owner_free.1

theorem current_header_free_exactly_once :
    freed.current = none ∧ freed.ownerCredits = [] ∧ freed.releases = [3,2,1] ∧
    freed.returned = packages 8 ∧ ¬ Free freed (nextEpoch (nextEpoch e4 to8) to16) :=
  ⟨rfl,rfl,rfl,rfl,free_cannot_be_repeated _ _ _⟩

theorem live_child_cannot_be_dropped_at_teardown : ¬ Free after8 (nextEpoch e4 to8) := by
  intro f
  have no : after8.values ≠ [] := by decide
  exact no f.2.2.1

theorem wrong_backing_origin_cannot_be_freed : ¬ Free taken e4 := by
  intro f
  have eq := f.2.1
  have no : taken.current ≠ some e4 := by decide
  exact no eq

theorem item_pointer_is_not_current_free_base :
    ¬ FreeAt taken (nextEpoch (nextEpoch e4 to8) to16) 1032 := by
  intro f
  have no : 1032 ≠ (nextEpoch (nextEpoch e4 to8) to16).address := by decide
  exact no f.2

def twiceReleased := {freed with releases := [3,3,2,1]}

theorem duplicated_release_ledger_rejected : ¬ WellFormed twiceReleased := by
  intro wf
  have no : ¬ twiceReleased.releases.Nodup := by decide
  exact no wf.uniqueReleases

theorem old_epoch_id_cannot_be_reused : ¬ Grow after8 (nextEpoch e4 to8) ⟨1,1000,16⟩ :=
  history_reuse_blocks_grow (by decide)


theorem fake_bounded_metadata_still_has_no_extra_element :
    plausibleFake.len ≤ plausibleFake.cap ∧
    ¬ CurrentRoot plausibleFake (token (nextEpoch e4 to8) 4) d := by
  refine ⟨by decide,?_⟩
  rintro ⟨e,eq,_,i,bound,same⟩
  have ee : e = nextEpoch e4 to8 := (Option.some.inj eq).symm
  subst e
  have ii := congrArg (fun p : PtrToken => p.incarnation.index) same
  simp [token,incarnation] at ii
  have bl : i < 4 := by simpa [plausibleFake,after8,candidate,pre4,packages] using bound
  omega

theorem old_span_descriptor_is_not_new_span :
    ¬ CurrentSpan {after8 with loans := {d}} e4 4 := by
  intro h
  have no : (after8.current : Option Epoch) ≠ some e4 := by decide
  exact no h.1

def resizedFirst : PhysicalState where
  world := projectedWorld after8 (fun _ => {⟨0⟩})
  placement := fun l => if l = (⟨0⟩ : RootLocationId) then some ⟨region e4,{⟨0⟩}⟩ else none

theorem realloc_first_then_old_source_is_not_physical_wellFormed :
    ¬ PhysicalWellFormed (fun l => l = (⟨0⟩ : RootLocationId)) resizedFirst := by
  intro wf
  have live := accepted_backing_requires_old_source_region wf
    (l := (⟨0⟩ : RootLocationId)) (pl := ⟨region e4,{⟨0⟩}⟩) (by simp [resizedFirst])
  have dead : region e4 ∉ resizedFirst.world.liveRegions := by decide
  exact dead live

def sameAddressFullWorld : World where
  liveRegions := {region e4,region (nextEpoch e4 to8)}
  bytes := fun r => if r = region e4 then fullBytes e4 else fullBytes (nextEpoch e4 to8)
  access := fun _ => ⟨true,true⟩

theorem same_address_simultaneous_full_epochs_alias : ¬ RegionsDisjoint sameAddressFullWorld := by
  apply aliasing_live_epochs_are_not_safe (a := region e4) (b := region (nextEpoch e4 to8))
  · decide
  · decide
  · decide
  · decide

def forceWorld8to16 : World where
  liveRegions := {region (nextEpoch e4 move8),region (nextEpoch (nextEpoch e4 move8) move16)}
  bytes := fun r => if r = region (nextEpoch e4 move8) then fullBytes (nextEpoch e4 move8)
    else fullBytes (nextEpoch (nextEpoch e4 move8) move16)
  access := fun _ => ⟨true,true⟩

theorem force_second_allocation_before_end_is_disjoint : RegionsDisjoint forceWorld8to16 := by
  intro r hr q hq ne
  have rs : r = region (nextEpoch e4 move8) ∨ r = region (nextEpoch (nextEpoch e4 move8) move16) := by
    simpa [forceWorld8to16] using hr
  have qs : q = region (nextEpoch e4 move8) ∨ q = region (nextEpoch (nextEpoch e4 move8) move16) := by
    simpa [forceWorld8to16] using hq
  rcases rs with rfl|rfl <;> rcases qs with rfl|rfl
  · exact False.elim (ne rfl)
  · decide
  · decide
  · exact False.elim (ne rfl)


/-- The twelve-record checkpoint is reconstructed, not a certified push trace. -/
def full12 : State := {after16 with values := packages 12,len := 12}

theorem twelve_record_checkpoint_wellFormed : WellFormed full12 := by
  constructor
  · decide
  · decide
  · decide
  · intro g mem
    have cases : g = 2 ∨ g = 1 := by
      simpa [full12,after16,candidate,full8,after8,pre4,e4,to8,nextEpoch] using mem
    rcases cases with rfl|rfl <;> decide

theorem twelve_record_checkpoint_has_accepted_physical_partition :
    PhysicalWellFormed (LiveLocation (nextEpoch (nextEpoch e4 to8) to16) 12)
      (physicalFor (nextEpoch (nextEpoch e4 to8) to16) 12) :=
  epoch_physical_wellFormed _ _ (by decide)

theorem eight_element_grow_has_accepted_physical_partition :
    PhysicalWellFormed (LiveLocation (nextEpoch (nextEpoch e4 to8) to16) full8.values.length)
      (physicalFor (nextEpoch (nextEpoch e4 to8) to16) full8.values.length) :=
  grow_has_accepted_physical_post_invariant grow8_to16

theorem twelve_record_read_oracle_is_data_policy :
    (full12.values[7]).id = ⟨7⟩ ∧ (full12.values[7]).data = 122 := by decide

end
end NewLang.Adjunct.ArrayEpoch.Counterexample
