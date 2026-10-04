import CORALean.ContSet.ConZonotope.Float.Operations.SupportBound

/-!
# `ConZonotope.boundDot` bounds the support function

Every point of the float constrained zonotope reads at most the bound in the
direction, whatever weights the simplex proposed: the certificate is checked
(`boundDotWeights_le`). An upper bound only; not claimed to be the support
function, which it reaches only up to rounding and only when the simplex's
weights are optimal.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.boundDot_le [ToRat 𝕋] (cZ : ConZonotope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ cZ.construct, c x ≤ toReal (cZ.boundDot a hc).val :=
  (cZ.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
