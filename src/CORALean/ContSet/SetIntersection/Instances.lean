import CORALean.ContSet.SetIntersection.Theorems.MtimesOuter
import CORALean.ContSet.SetIntersection.Theorems.PlusOuter
import CORALean.ContSet.SetIntersection.Theorems.ReduceOuter

/-!
# What `SetIntersection` instantiates

`ContSet` is already at `SetIntersection.lean`, since the type's own docstring
needs what it denotes. `Mtimes`, `Plus` and `Reduce` follow whenever the
member type `S` has them, each the branch-wise operation from `Operations/`
paired with the outer guarantee `Theorems/` proves for it.

`Contains`/`IsDisjoint` lift both ways. As the *computed* set, `S :=
SetIntersection S'`: conservative both ways, one member already answering
being enough. As the *container*, `T := SetIntersection T'`: `contains`
exact, needing every member; `isDisjoint` conservative. Both instantiate
`Contains (SetIntersection T') (SetIntersection S')` at once, so the
container pair carries `(priority := low)`, exactly as `SetUnion`'s own two
pairs do: the computed-set reading is tried first, uniformly across both
files.

Computable throughout, for the same reason as `SetUnion`: every field is
`List.map`/`List.all`/`List.any` over whatever `S`'s own instance computes.
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
    Mtimes 𝕄 (fun n => SetIntersection (S n)) where
  mtimes := SetIntersection.mtimes
  mtimes_outer := SetIntersection.mtimes_outer

variable {S α : Type} [AddCommGroup α] [Module ℝ α] [ContSet S α]

instance [Plus S α] : Plus (SetIntersection S) α where
  plus := SetIntersection.plus
  plus_outer := SetIntersection.plus_outer

instance [Reduce S α] : Reduce (SetIntersection S) α where
  reduce := SetIntersection.reduce
  reduce_outer := SetIntersection.reduce_outer

variable {T α : Type} [ContSet T α] [ContSet S α]

/-- Conservative as a computed set: if `t` contains one member, it contains
the (smaller) intersection too — `Set.iInter₂_subset` shrinks first. -/
instance [Contains T S] : Contains T (SetIntersection S) where
  contains t I := I.sets.any (Contains.contains t ·)
  contains_sound t I h := by
    obtain ⟨s, hs, h⟩ := List.any_eq_true.mp h
    exact (Set.iInter₂_subset s hs).trans (Contains.contains_sound t s h)

/-- Conservative as a computed set: if `t` misses one member, it misses the
(smaller) intersection too. -/
instance [IsDisjoint T S] : IsDisjoint T (SetIntersection S) where
  isDisjoint t I := I.sets.any (IsDisjoint.isDisjoint t ·)
  isDisjoint_sound t I h := by
    obtain ⟨s, hs, h⟩ := List.any_eq_true.mp h
    exact (IsDisjoint.isDisjoint_sound t s h).mono_left (Set.iInter₂_subset s hs)

/-- Exact as a container: `s` sits in the intersection iff it sits in every
member — `Set.subset_iInter₂`, one branch at a time. -/
instance (priority := low) [Contains T S] : Contains (SetIntersection T) S where
  contains I s := I.sets.all (Contains.contains · s)
  contains_sound I s h := by
    refine Set.subset_iInter₂ fun t ht => ?_
    exact Contains.contains_sound t s (List.all_eq_true.mp h t ht)

/-- Conservative as a container: `true` only if `s` misses one member, that
member's disjointness shrunk onto the (smaller) intersection. -/
instance (priority := low) [IsDisjoint T S] : IsDisjoint (SetIntersection T) S where
  isDisjoint I s := I.sets.any (IsDisjoint.isDisjoint · s)
  isDisjoint_sound I s h := by
    obtain ⟨t, ht, h⟩ := List.any_eq_true.mp h
    exact (IsDisjoint.isDisjoint_sound t s h).mono_right (Set.iInter₂_subset t ht)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
