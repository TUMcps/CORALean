module

public import CORALean.ContSet.Zonotope.Float.Theorems.MethCResidualBound
public import CORALean.ContSet.Zonotope.Float.Operations.MethCQ

@[expose] public section

/-!
# `methCQ` bounds every absolute row sum of `1 - H P`

The entries are bounded by `methCResidual`, a row of them is summed upward, and the largest of the
sums is taken exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n h : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.methCQ_bound (H P : Mat 𝕋 n n) (i : Fin n) :
    ∑ j, |(1 - toRealMat H * toRealMat P) i j|
      ≤ toReal (Zonotope.methCQ H P) := by
  refine le_trans (Finset.sum_le_sum fun j _ => Zonotope.methCResidual_bound H P i j) ?_
  refine le_trans (sum_le_sumUp fun j => Zonotope.methCResidual H P i j) ?_
  exact le_maximumOver (fun i => sumUp fun j => Zonotope.methCResidual H P i j) i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
