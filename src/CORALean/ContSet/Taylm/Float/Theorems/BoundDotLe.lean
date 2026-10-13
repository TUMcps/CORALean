import CORALean.ContSet.Taylm.Float.Operations.BoundDot

/-!
# `Taylm.boundDot` bounds the support function

No point of the range set reads more than the float value, an upper bound and nothing tighter.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.boundDot_le {c : Vec ℝ m →ₗ[ℝ] ℝ} (a : Vec 𝕋 m) (T : Fin m → Taylm 𝕋 n)
    (hc : ∀ x : Vec ℝ m, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ Taylm.construct T, c x ≤ toReal (Taylm.boundDot a T hc).val :=
  (Taylm.boundDot a T hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
