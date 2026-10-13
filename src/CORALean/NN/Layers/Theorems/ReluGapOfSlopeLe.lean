import CORALean.Global.Float.SoundFloatArithmetic
import CORALean.NN.Layers.Definitions.Relu
import CORALean.NN.Layers.Operations.ReluGapUp

/-!
# The rounded gap bounds the exact one

`reluGapUp` rounds each of its two terms up — the difference by `subUp`, the negated product by
negating a rounded-down one — and `maximum` is exact, so it is at least `reluGapOfSlope` at the
values the stored arguments denote.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

-- not `Matrix`: its `zero` would make `FloatOps.zero` ambiguous
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋]


-- =======================================  MAIN THEOREM  ======================================= --

theorem reluGapOfSlope_le (lam l u : 𝕋) :
    Real.reluGapOfSlope (toReal lam) (toReal l) (toReal u)
      ≤ toReal (reluGapUp lam l u) := by -- --- PROOF ---
  have hexp : (1 - toReal lam) * toReal u = toReal u - toReal lam * toReal u := by ring
  have h1 : (1 - toReal lam) * toReal u ≤ toReal (subUp u (mulDown lam u)) := by
    have ha := sub_le_subUp u (mulDown lam u)
    have hb := mulDown_le_mul lam u
    rw [hexp]
    linarith
  have h2 : -(toReal lam * toReal l) ≤ toReal (neg (mulDown lam l)) := by
    have hb := mulDown_le_mul lam l
    rw [toReal_neg]
    linarith
  rw [Real.reluGapOfSlope, reluGapUp, toReal_maximum]
  exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
