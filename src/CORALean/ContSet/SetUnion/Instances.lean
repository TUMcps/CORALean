import CORALean.ContSet.SetUnion.Theorems.API

/-!
# What `SetUnion` instantiates

`ContSet` is already at `SetUnion.lean`, since the type's own docstring needs
what it denotes. `Mtimes`, `Plus` and `Reduce` follow whenever the member
type `S` has them, each the branch-wise operation from `Operations/` paired
with the guarantee `Theorems/` proves for it.

Computable throughout: every field here is `List.map` or `×ˢ` over whatever
`S`'s own instance computes, so a float member type makes every instance below
compute in turn, with nothing rounded and no error box to carry.
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

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
