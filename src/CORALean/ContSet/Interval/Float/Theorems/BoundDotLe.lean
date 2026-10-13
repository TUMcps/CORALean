import CORALean.ContSet.Interval.Float.Operations.BoundDot

/-!
# `Interval.boundDot` bounds the support function

No point of the box reads more than the float value, which is an upper bound and
nothing tighter: the real layer's `Interval.supportBound_attained` is the
statement that the exact value is reached.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.boundDot_le (I : Interval (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ I.construct, c x ≤ toReal (I.boundDot a hc).val :=
  (I.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
