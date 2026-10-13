import CORALean.ContSet.PolyZonotope.Real.Operations.IsPolytopeCex
import Mathlib.Algebra.BigOperators.Fin

/-!
# The monomials of `isPolytopeCex`

Its exponent matrix is `[[1,0,1],[0,1,0],[0,0,1]]`; the monomial product over three factors.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.isPolytopeCex_monomial (I : Fin 3 → ℝ) (j : Fin 3) :
    PolyZonotope.monomial ![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]] I j =
      I 0 ^ (![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]] 0 j : ℕ) *
      I 1 ^ (![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]] 1 j : ℕ) *
      I 2 ^ (![![1, 0, 1], ![0, 1, 0], ![0, 0, 1]] 2 j : ℕ) := Fin.prod_univ_three _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
