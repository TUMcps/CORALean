import CORALean.ContSet.ConPolyZono.Float.Operations.PlusA
import CORALean.ContSet.ConPolyZono.Float.Operations.UnionConCoef

/-!
# `ConPolyZono.unionUpperA`

The two selector rows of [1, Thm. 1], as `Real.ConPolyZono.unionUpperA` lays them
out: `α₁α₂ = 1` with its one coefficient, and the selector polynomial with the
integer coefficients of `unionConCoef`, side by side.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The two selector rows, side by side. -/
def ConPolyZono.unionUpperA (p₁ p₂ : ℕ) :
    Mat 𝕋 (1 + 1) (1 + (2 + (p₁ + p₁ + (p₂ + p₂ + (p₁ * p₂ + p₁ * p₂))))) :=
  ConPolyZono.plusA (fun _ _ => one) (fun _ l => ConPolyZono.unionConCoef p₁ p₂ l)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
