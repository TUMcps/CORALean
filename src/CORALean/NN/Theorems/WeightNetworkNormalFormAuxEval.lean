import CORALean.NN.Operations.WeightNetworkNormalFormAux
import CORALean.NN.Operations.WeightNetworkEval
import CORALean.NN.Theorems.WeightAccPushLinearEval
import CORALean.NN.Theorems.WeightAccPushAffineEval
import CORALean.NN.Theorems.WeightAccLayerEval

/-!
# `getNormalForm`'s loop keeps the function

Starting from an accumulator, the loop's network computes what the remaining network does after
the accumulated map, exactly: the induction on the layers, one case per layer type.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {α : Type} [Semiring α] {n m k d : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The loop's network is the remaining network after the accumulated map. -/
theorem WeightNetwork.normalFormAux_eval : ∀ {n d k : ℕ} (acc : WeightAcc α n d)
    (N : WeightNetwork α d k) (x : Fin n → α), (N.normalFormAux acc).eval x = N.eval (acc.eval x)
  | _, _, _, .id, .nil, _ => rfl
  | _, _, _, .aff _ _, .nil, _ => by simp [WeightNetwork.normalFormAux, WeightNetwork.eval,
      WeightLayer.eval, WeightAcc.eval]
  | _, _, _, acc, .cons (.linear W b) rest, x => by
    rw [WeightNetwork.normalFormAux, normalFormAux_eval, WeightAcc.pushLinear_eval]; rfl
  | _, _, _, acc, .cons (.elementwiseAffine s o) rest, x => by
    rw [WeightNetwork.normalFormAux, normalFormAux_eval, WeightAcc.pushAffine_eval]; rfl
  | _, _, _, acc, .cons .identity rest, x => by
    rw [WeightNetwork.normalFormAux, normalFormAux_eval]; rfl
  | _, _, _, acc, .cons (.activation f) rest, x => by
    simp only [WeightNetwork.normalFormAux, WeightNetwork.eval, normalFormAux_eval]
    show rest.eval (fun i => f (acc.layer.eval x i)) = rest.eval (fun i => f (acc.eval x i))
    rw [WeightAcc.layer_eval]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
