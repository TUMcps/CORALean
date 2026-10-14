module

public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The scaling of the Lipschitz-constrained linear layer, over a float scalar

`Layer.lipConstrScale` bracketed: the row sum is rounded down and up, so the divisor
`max(1, λ⁻¹ Σⱼ |Wᵢⱼ|)` is bracketed, and so is its reciprocal. Needs `0 < λ` to be sound.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A box around the diagonal of `N`, `1 ./ max(1, λ⁻¹ Σⱼ |Wᵢⱼ|)`, each end rounded outward. -/
def Layer.lipConstrScaleFloat (W : Mat 𝕋 m n) (lam : 𝕋) : Float.Interval (Vec 𝕋 m) where
  inf i := divDown one (maximum one (divUp (radius W i) lam))
  sup i := divUp one (maximum one (divDown (sumDown fun j => absolute (W i j)) lam))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
