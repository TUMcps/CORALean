module

public import CORALean.ContSet.Zonotope.Real.Operations.MinnormOffset

@[expose] public section

/-!
# The unit-row offsets are nonnegative

A sum of absolute values over a square root: the lower bound `0` that makes `minnorm`, an
infimum of offsets, a nonnegative number attained.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.minnormOffset_nonneg (Z : Zonotope (Vec ℝ (n + 1))) (S : Fin n → Fin Z.h) :
    0 ≤ Z.minnormOffset S :=
  div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
