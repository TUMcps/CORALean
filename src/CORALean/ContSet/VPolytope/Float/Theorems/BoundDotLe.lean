import CORALean.ContSet.VPolytope.Float.Operations.SupportBound

/-!
# `VPolytope.boundDot` bounds the support function

No point of the set reads more than the float value, an upper bound only: the
real layer's `VPolytope.supportBound_attained` is the statement that the exact
value is reached.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.boundDot_le (P : VPolytope 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ P.construct, c x ≤ toReal (P.boundDot a hc).val :=
  (P.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
