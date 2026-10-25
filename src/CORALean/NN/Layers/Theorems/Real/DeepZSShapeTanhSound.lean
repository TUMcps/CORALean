module

public import CORALean.NN.Layers.Theorems.Real.DeepZSShapeSound
public import CORALean.NN.Layers.Theorems.Real.HasDerivAtTanh
public import CORALean.NN.Layers.Theorems.Real.SigmoidNeg
public import CORALean.NN.Layers.Theorems.Real.TanhDerivSShape
public import CORALean.NN.Layers.Theorems.SShapeUnimodal

@[expose] public section

/-!
# DeepZ's transformer is sound for tanh

[1, Sec. 3.3]: tanh is S-shaped too, and [1, Thm. 3.2] applies with `f' = 1 - tanh²`. The
derivative `hasDerivAt_tanh` gives, `4 σ'(2t)`, is that by `tanh t = 2 σ(2t) - 1`; it is even
and falls away from `0`, so `deepZSShape_sound` applies at `x' = 0`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* DeepZ's transformer is sound for tanh

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

theorem deepZSShape_tanh_sound : -- --- CONCL ---
    (deepZSShape Real.tanh fun t => 1 - Real.tanh t ^ 2).IsSound Real.tanh := by -- --- PROOF ---
  -- `4 σ'(2t) = 1 - (2 σ(2t) - 1)²`
  have hd : ∀ t, HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := fun t => by
    have h := hasDerivAt_tanh t
    have heq : 4 * sigmoidDeriv (2 * t) = 1 - Real.tanh t ^ 2 := by
      rw [tanh_eq_sigmoid, sigmoidDeriv, sigmoid_neg]
      ring
    rwa [heq] at h
  exact deepZSShape_sound hd tanhDeriv_sShape.unimodal.1 tanhDeriv_sShape.unimodal.2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
