module

public import CORALean.ContSet.HPolytope.Float.HPolytope

@[expose] public section

/-!
# A negated constraint matrix, applied to a point
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Negation is exact, so the negated rows read the negated products. -/
theorem HPolytope.mulVec_neg (M : Mat 𝕋 m n) (x : Vec ℝ n) :
    toRealMat (fun i j => neg (M i j)) *ᵥ x = -(toRealMat M *ᵥ x) := by
  funext i
  show ∑ k, toReal (neg (M i k)) * x k = -∑ k, toReal (M i k) * x k
  simp [toReal_neg, Finset.sum_neg_distrib]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
