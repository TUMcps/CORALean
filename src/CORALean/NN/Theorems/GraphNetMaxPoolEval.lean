module

public import CORALean.NN.Operations.GraphNetMaxPool
public import CORALean.NN.Layers.Theorems.Real.MaxEqAddReluSub
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# `GraphNet.maxPool` is the maximum of the two operands

The network `relu(D x)` plus the residual `B x` computes `max((D + B) x, B x)`, by
`max_eq_add_relu_sub`: with `A = D + B`, each output is the larger of `A x` and `B x`.

## Inputs
* `D` – the difference of the operands' maps
* `B` – the second operand's map
* `x` – the point the network reads

## Hypotheses
* none

## Conclusion
* the network's output is the maximum, entrywise
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem GraphNet.maxPool_eval (D B : Mat ℝ m n) (x : Vec ℝ n) : -- --- CONCL ---
    (GraphNet.maxPool D B).eval (GraphEnv.cons x fun i => i.elim0) =
      fun i => max (((D + B) *ᵥ x) i) ((B *ᵥ x) i) := by -- --- PROOF ---
  funext i
  rw [max_eq_add_relu_sub]
  simp [GraphNet.eval, GraphNet.maxPool, GraphLayer.preact, GraphAct.apply, GraphEnv.cons,
    Matrix.mulVec, dotProduct, Matrix.one_apply, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib, relu]
  -- the two sums in the other order, equal up to the unfolded instances
  rw [add_comm]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
