module

public import CORALean.ContSet.Polygon.Float.Operations.BoundDot

@[expose] public section

/-!
# `Polygon.boundDot` bounds the support function

No point of the polygon reads more than the float value, an upper bound only.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Polygon.boundDot_le (P : Polygon 𝕋) {c : Vec ℝ 2 →ₗ[ℝ] ℝ} (a : Vec 𝕋 2)
    (hc : ∀ x : Vec ℝ 2, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ ContSet.construct P, c x ≤ toReal (P.boundDot a hc).val :=
  (P.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
