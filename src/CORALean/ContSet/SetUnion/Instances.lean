import CORALean.ContSet.SetUnion.Theorems.MtimesOuter
import CORALean.ContSet.SetUnion.Theorems.PlusOuter
import CORALean.ContSet.SetUnion.Theorems.ReduceOuter

/-!
# What `SetUnion` instantiates

`ContSet` is already at `SetUnion.lean`, since the type's own docstring needs
what it denotes. `Mtimes`, `Plus` and `Reduce` follow whenever the member
type `S` has them, each the branch-wise operation from `Operations/` paired
with the guarantee `Theorems/` proves for it.

`OfPoint` is a one-member union.
`Contains`/`IsDisjoint` lift both ways. As the *computed* set, `S := SetUnion
S'`: exact, checking every member. As the *container*, `T := SetUnion T'`:
`contains` by any member (conservative), `isDisjoint` by every member
(exact). Both instantiate `Contains (SetUnion T') (SetUnion S')` at once, so
the container pair carries `(priority := low)`: the computed-set reading is
tried first, the same rule `SetIntersection` uses for its own two pairs.

Computable throughout: every field here is `List.map`/`List.all`/`List.any` over whatever `S`'s
own instance computes, so a float member type makes every instance compute in turn, with nothing
rounded and no error box to carry.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- ========================================  INSTANCES  ========================================= --

instance {𝕄 : ℕ → ℕ → Type} {S : ℕ → Type}
    [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [∀ n, ContSet (S n) (Vec ℝ n)] [Mtimes 𝕄 S] :
    Mtimes 𝕄 (fun n => SetUnion (S n)) where
  mtimes := SetUnion.mtimes
  mtimes_outer := SetUnion.mtimes_outer

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α]

instance [Plus S α] : Plus (SetUnion S) α where
  plus := SetUnion.plus
  plus_outer := SetUnion.plus_outer

instance [Reduce S α] : Reduce (SetUnion S) α where
  reduce := SetUnion.reduce
  reduce_outer := SetUnion.reduce_outer

/-- A singleton is a union of one singleton. -/
instance [OfPoint S α] : OfPoint (SetUnion S) α where
  ofPoint v := ⟨[OfPoint.ofPoint v]⟩
  mem_ofPoint v := SetUnion.mem_construct.mpr ⟨_, List.mem_singleton_self _, OfPoint.mem_ofPoint v⟩

variable {T α : Type} [ContSet T α] [ContSet S α]

/-- Exact as a computed set: `t` contains the union iff it contains every
member. Default priority: tried before the container reading below. -/
instance [Contains T S] : Contains T (SetUnion S) where
  contains t u := u.sets.all (Contains.contains t ·)
  contains_sound t u h := by
    refine Set.iUnion₂_subset fun s hs => ?_
    exact Contains.contains_sound t s (List.all_eq_true.mp h s hs)

/-- Exact as a computed set: `t` misses the union iff it misses every
member. Default priority: tried before the container reading below. -/
instance [IsDisjoint T S] : IsDisjoint T (SetUnion S) where
  isDisjoint t u := u.sets.all (IsDisjoint.isDisjoint t ·)
  isDisjoint_sound t u h := by
    refine Set.disjoint_iUnion₂_left.mpr fun s hs => ?_
    exact IsDisjoint.isDisjoint_sound t s (List.all_eq_true.mp h s hs)

/-- Conservative as a container: `true` only if one member already contains
`s`, widened to the whole union by `Set.subset_iUnion₂_of_subset`. -/
instance (priority := low) [Contains T S] : Contains (SetUnion T) S where
  contains u s := u.sets.any (Contains.contains · s)
  contains_sound u s h := by
    obtain ⟨t, ht, h⟩ := List.any_eq_true.mp h
    exact Set.subset_iUnion₂_of_subset t ht (Contains.contains_sound t s h)

/-- Exact as a container: the union misses `s` iff every member does —
`Set.disjoint_iUnion₂_right`, one branch at a time. -/
instance (priority := low) [IsDisjoint T S] : IsDisjoint (SetUnion T) S where
  isDisjoint u s := u.sets.all (IsDisjoint.isDisjoint · s)
  isDisjoint_sound u s h := by
    refine Set.disjoint_iUnion₂_right.mpr fun t ht => ?_
    exact IsDisjoint.isDisjoint_sound t s (List.all_eq_true.mp h t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
