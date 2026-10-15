module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# `Zonotope.genSelection`

`(c, g_sort⁽¹⁾, …, g_sort⁽ˣⁱ⁾)`: the first `ξ` generators of `Z` in the order a
permutation puts them, at a center of the caller's choosing. [1, Alg. 1] builds
one at each step of its second loop, to test at `c⁽ˢ⁾`, and returns the last at
`c⁽ᵐ⁾` — so the center is an argument rather than `Z`'s own.

`min ξ Z.h`, not `ξ`: the count is what a loop carries and a loop may be asked
for more generators than there are. Capping keeps the operation total, and
`Alg. 1`'s loops never reach the cap, both stopping at `ξ < n_m`.

## References

* [1] M. Althoff. "On Computing the Minkowski Difference of Zonotopes".
      arXiv, 2015.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first `ξ` generators of `Z` under `σ`, at the center `c`. -/
def Zonotope.genSelection (Z : Zonotope α) (σ : Equiv.Perm (Fin Z.h)) (c : α)
    (ξ : ℕ) : Zonotope α where
  h := min ξ Z.h
  c := c
  G := fun i => Z.G (σ (Fin.castLE (min_le_right ξ Z.h) i))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
