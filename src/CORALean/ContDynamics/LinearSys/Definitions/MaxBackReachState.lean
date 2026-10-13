module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContSet.ConZonotope.Real.Instances
public import CORALean.ContSet.Zonotope.Real.Instances

@[expose] public section

/-!
# `Alg. 2`'s loop state

`MaxBackReachState`: what one iteration of [1, Alg. 2] hands the next.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of
      Perturbed Continuous-Time Linear Systems Using Set Propagation". arXiv:2310.19083,
      2023.
-/

-- Authors:       Claude Sonnet 5
-- Written:       19-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 2] hands the next. -/
structure LinearSys.MaxBackReachState (n : ℕ) where
  /-- `t_k`, line 7. -/
  t : ℝ
  /-- `Z̲_U(t_k)`, line 8. -/
  ZU : Zonotope (Vec ℝ n)
  /-- `Ẑ_{W₀}(t_k)`, line 9. -/
  ZW₀ : Zonotope (Vec ℝ n)
  /-- `Ẑ_W(τ_{k-1})`, line 10. -/
  ZW : Zonotope (Vec ℝ n)
  /-- `R̂^{∃∀}(-τ_{k-1})`, line 12. -/
  R : ConZonotope (Vec ℝ n)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
