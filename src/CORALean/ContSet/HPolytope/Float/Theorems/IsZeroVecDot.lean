import CORALean.ContSet.HPolytope.Float.Operations.IsZeroVec
import CORALean.ContSet.HPolytope.Float.Theorems.EqScalarEq

/-!
# A certified zero row is the zero functional

Each entry reads `0`, so the dot product with any point is `0`.
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.isZeroVec_dot {v : Vec 𝕋 n} (h : HPolytope.isZeroVec v = true) (x : Vec ℝ n) :
    ∑ j, toReal (v j) * x j = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := List.all_eq_true.mp h j (List.mem_finRange j)
  rw [HPolytope.toReal_eq_of_eqScalar hj, toReal_zero, zero_mul]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
