import CORALean.NN.Layers.Sigmoid

/-!
# The sigmoid is nonexpansive

`abs_sigmoidDeriv_le_one` is already there — `σ' = σ · σ (-·)` is a product of
two numbers in `(0, 1)` — and the mean value theorem turns a derivative bound
into a Lipschitz bound on all of ℝ, the domain being convex.

The constant is `1` and not `1/4`, which is the true supremum of `σ'`. Nothing
downstream reads the number, and `1` is what the existing global bound gives
without a second argument about where `σ'` is maximal.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem lipschitzWith_sigmoid : LipschitzWith 1 sigmoid := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_sigmoid t).differentiableAt) fun t => ?_
  -- the derivative is named, so the bound is the one already proved of it
  rw [(hasDerivAt_sigmoid t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs]
  exact abs_sigmoidDeriv_le_one t

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
