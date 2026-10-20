module

public import CORALean.NN.Operations.SmoothNetworkEval

@[expose] public section

/-!
# CORA's `nonlinearSysDT` drops the scale of an elementwise affine layer

CORA's conversion adds `offset` and drops `scale`, though the layer's own `evaluateNumeric` is
`scale .* input + offset`: for `scale = 2`, `offset = 0` it answers `x` where the layer computes
`2 x`, so `func(x,0) = evaluate(net,x)`, which CORA states, fails.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the layer computes a different function than CORA's conversion
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's conversion adds `offset` and drops `scale`, so for `scale = 2`, `offset = 0` it
answers `x`, where the layer computes `2 x`. -/
theorem SmoothNetwork.elementwiseAffine_cora_counterexample :
    ∃ (scale offset x : Vec ℝ 1),
      (SmoothNetwork.elementwiseAffine scale offset .output).eval x ≠
        fun i => x i + offset i := by
  refine ⟨fun _ => 2, fun _ => 0, fun _ => 1, fun h => ?_⟩
  have := congrFun h 0
  norm_num [SmoothNetwork.eval] at this

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
