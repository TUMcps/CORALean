module

public import CORALean.ContSet.HPolytope.Float.Operations.IsZeroVec
public import CORALean.ContSet.HPolytope.Float.Theorems.EqScalarEq

@[expose] public section

/-!
# A certified zero row is the zero functional

Each entry reads `0`, so the dot product with any point is `0`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
