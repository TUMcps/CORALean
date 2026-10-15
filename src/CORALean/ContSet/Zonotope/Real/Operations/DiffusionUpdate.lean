module

public import CORALean.ContSet.Zonotope.Real.Operations.AndAveraging
public import CORALean.ContSet.Zonotope.Real.Operations.AveragingWeights
public import CORALean.ContSet.Zonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `Zonotope.diffusionUpdate`

The diffusion update of one node, Step 2 of [1, Alg. 1] and of [1, Alg. 2]: the weights `𝔴` of
[1, Prop. 1] (`averagingWeights`, the minimizer of `‖Ǵ‖_F` among weights of sum one), the weighted
average of the `m_i` shared zonotopes `Z̄ʲ` of its neighbourhood (`andAveraging`, the center and
generators of [1, Thm. 1]), and the order reduction `↓_q`, here CORA's `reduce` to order `o`, as
[1] leaves the rule open.

## References

* [1] A. Alanwar, J. J. Rath, H. Said, K. H. Johansson and M. Althoff. "Distributed Set-Based
      Observers Using Diffusion Strategies". Journal of the Franklin Institute,
      360(10):6976-6993, 2023. arXiv:2003.10347.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def Zonotope.diffusionUpdate (o : ℕ) (Zb : Fin m → Zonotope (Vec ℝ n)) :
    Zonotope (Vec ℝ n) :=
  let w : Fin m → ℝ := Zonotope.averagingWeights Zb                     -- 𝔴 = argmin ‖Ǵ‖_F, Eq. 19
  let Ž : Zonotope (Vec ℝ n) := Zonotope.andAveraging Zb w              -- ć and Ǵ, Eqs. 14 and 15
  Ž.reduce o                                                            -- Ĝ = ↓_q G̃

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
