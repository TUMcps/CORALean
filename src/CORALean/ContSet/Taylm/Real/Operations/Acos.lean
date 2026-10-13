import CORALean.ContSet.Taylm.Real.Operations.Taylor
import CORALean.ContSet.Taylm.Real.Operations.ConstCoef
import CORALean.ContSet.Taylm.Real.Operations.Mag
import CORALean.Global.ElementaryDerivBounds

/-!
# `Taylm.acos`

CORA's `acos`: `acos' = -asin'`, so the derivative bound is `asin`'s, and so is the
domain.

A Taylor model of `arccos ∘ f`, [1, Def. 3 (arccos)], expanded directly rather than as
`π/2 - arcsin`.

## References

* [1] K. Makino and M. Berz. "Taylor Models and Other Validated Functional Inclusion
      Methods". International Journal of Pure and Applied Mathematics, 4(4):379-452, 2003.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Taylm.acos (T : Taylm n) : Taylm n :=
  T.taylor Real.arccos T.constCoef
    ((asinDom T.maxOrder).eval T.mag * ((√(1 - T.mag ^ 2))⁻¹) ^ (2 * T.maxOrder + 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
