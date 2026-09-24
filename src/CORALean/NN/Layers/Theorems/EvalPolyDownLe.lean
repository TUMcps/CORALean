import CORALean.NN.Layers.Definitions.EvalPoly
import CORALean.NN.Layers.Operations.EvalPolyDown
import CORALean.NN.Layers.Theorems.MulRangeDownLe
import CORALean.NN.Layers.Theorems.PowRangeBounds

/-!
# A polynomial is above its lower evaluation

Term by term against the power's bracket, and the sum rounded down.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem evalPolyDown_le (c : Fin (n + 1) → 𝕋) (t : 𝕋) :
    toReal (evalPolyDown c t) ≤ Real.evalPoly (fun k => toReal (c k)) (toReal t) := by
  show toReal (sumDown _) ≤ ∑ i, toReal (c i) * toReal t ^ (i : ℕ)
  refine le_trans (sumDown_le_sum _) (Finset.sum_le_sum fun i _ => ?_)
  exact mulRangeDown_le (powRange_bounds t (i : ℕ)).1 (powRange_bounds t (i : ℕ)).2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
