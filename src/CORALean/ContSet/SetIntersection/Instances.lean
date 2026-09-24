import CORALean.ContSet.SetIntersection.Theorems.API

/-!
# What `SetIntersection` instantiates

`ContSet` is already at `SetIntersection.lean`, since the type's own docstring
needs what it denotes. `Mtimes`, `Plus` and `Reduce` follow whenever the
member type `S` has them, each the branch-wise operation from `Operations/`
paired with the outer guarantee `Theorems/` proves for it.

Computable throughout, for the same reason as `SetUnion`: every field is
`List.map` or `×ˢ` over whatever `S`'s own instance computes.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
