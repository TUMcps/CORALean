import CORALean.NN.Layers.Definitions.Enclosure
import CORALean.NN.Layers.Definitions.ScaleRounding
import CORALean.NN.Layers.Definitions.Sigmoid
import CORALean.NN.Layers.Definitions.SigmoidRelaxation
import CORALean.NN.Layers.Operations.Sigmoid
import CORALean.NN.Layers.Theorems.Real.AbsSigmoidDerivLeOne
import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid

/-!
# The sigmoid is nonexpansive

`Real.abs_sigmoidDeriv_le_one` is already there — `σ' = σ · σ (-·)` is a product of
two numbers in `(0, 1)` — and the mean value theorem turns a derivative bound
into a Lipschitz bound on all of ℝ, the domain being convex.

The constant is `1` and not `1/4`, which is the true supremum of `σ'`. Nothing
downstream reads the number, and `1` is what the existing global bound gives
without a second argument about where `σ'` is maximal.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

theorem lipschitzWith_sigmoid : LipschitzWith 1 Real.sigmoid := by -- --- PROOF ---
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun t => (Real.hasDerivAt_sigmoid t).differentiableAt) fun t => ?_
  -- the derivative is named, so the bound is the one already proved of it
  rw [(Real.hasDerivAt_sigmoid t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs]
  exact Real.abs_sigmoidDeriv_le_one t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
