import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Operations.EvalPolyUp
import CORALean.NN.Layers.Theorems.LeMulRangeUp
import CORALean.NN.Layers.Theorems.PowRangeBounds

/-!
# A polynomial is below its upper evaluation

The mirror of `evalPolyDown_le`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem le_evalPolyUp (c : Fin (n + 1) → 𝕋) (t : 𝕋) :
    Real.evalPoly (fun k => toReal (c k)) (toReal t) ≤ toReal (evalPolyUp c t) := by
  show (∑ i, toReal (c i) * toReal t ^ (i : ℕ)) ≤ toReal (sumUp _)
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_le_sumUp _)
  exact le_mulRangeUp (powRange_bounds t (i : ℕ)).1 (powRange_bounds t (i : ℕ)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
