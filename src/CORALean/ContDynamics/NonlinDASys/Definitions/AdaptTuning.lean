import CORALean.ContDynamics.NonlinDASys.Definitions.LinPoint
import CORALean.ContDynamics.NonlinDASys.Definitions.HessData
import CORALean.ContDynamics.NonlinDASys.Definitions.AdaptPass

/-!
# The heuristics of the adaptive DAE algorithm

`linReach_adaptive` tunes the step and the tensor order by the `varphi` heuristics. None
carries a guarantee, so they are arguments the outer theorems quantify over, as in
`NonlinearSys.adaptStep`: the linearization `priv_linearize` (`taylor`), the interval Hessians of
the abstraction error ([1, Cor. 1], `hess`), the comparison of reals (`le`), `expFactor`, the
tuned step (`tune`, `aux_optimaldeltat`) and the next finite horizon (`nextH`, the controller).

## References

* [1] M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control, 59(2):371-383, 2014.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- The tuning heuristics of `linReach_adaptive`, none with a guarantee. -/
structure NonlinDASys.AdaptTuning (n p m q : ℕ) where
  /-- `priv_linearize`: the linearization at a start set. -/
  taylor : Zonotope (Vec ℝ n) → NonlinDASys.LinPoint n p m
  /-- The Hessian intervals over a joint set of `(x, y)` (`nlnsysDA.hessian`). -/
  hess : Zonotope (Vec ℝ n × Vec ℝ p) → NonlinDASys.HessData n p q
  /-- Comparison of reals, as the test `perfInd ≤ 1`. -/
  le : ℝ → ℝ → Bool
  /-- `expFactor`, the bloating of the admissible error. -/
  expFactor : ℝ
  /-- `aux_optimaldeltat`: the tuned step from the finite horizon and the first pass. -/
  tune : ℝ → NonlinDASys.AdaptPass n p → ℝ
  /-- The `varphi` controller: the next finite horizon from this one and the pass. -/
  nextH : ℝ → NonlinDASys.AdaptPass n p → ℝ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
