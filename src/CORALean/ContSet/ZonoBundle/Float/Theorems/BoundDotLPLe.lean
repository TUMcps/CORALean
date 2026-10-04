import CORALean.ContSet.ZonoBundle.Float.Operations.BoundDotLP

/-!
# `ZonoBundle.boundDotLP` bounds the support function

Every point of the bundle reads at most the bound in the direction. An upper
bound only: the linear program's value is reached only up to rounding and only
where the simplex's weights are optimal, which is not claimed.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] [ToRat 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.boundDotLP_le (zB : ZonoBundle 𝕋 n) (hk : 0 < zB.k)
    {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ zB.construct, c x ≤ toReal (zB.boundDotLP hk a hc).val :=
  (zB.boundDotLP hk a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
