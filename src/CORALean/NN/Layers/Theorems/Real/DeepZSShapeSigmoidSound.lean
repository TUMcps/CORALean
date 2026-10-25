module

public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeSound
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtSigmoid
public import CORALean.NN.Layers.Theorems.Real.SigmoidDerivSShape
public import CORALean.NN.Layers.Theorems.SShapeUnimodal

@[expose] public section

/-!
# DeepZ's transformer is sound for the sigmoid

[1, Thm. 3.2] at `f = σ`, `f' = σ(t) σ(-t)`, the paper's example and its [1, Fig. 2]:
the derivative is even and falls away from `0`, so it rises to `0` and falls after it, and
`deepZSShape_sound` applies at `x' = 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* DeepZ's transformer is sound for the sigmoid

## References

* [1] G. Singh, T. Gehr, M. Mirman, M. Püschel and M. Vechev. "Fast and Effective Robustness
      Certification". NeurIPS 2018.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem deepZSShape_sigmoid_sound : (deepZSShape sigmoid sigmoidDeriv).IsSound sigmoid :=
  deepZSShape_sound hasDerivAt_sigmoid sigmoidDeriv_sShape.unimodal.1
    sigmoidDeriv_sShape.unimodal.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
