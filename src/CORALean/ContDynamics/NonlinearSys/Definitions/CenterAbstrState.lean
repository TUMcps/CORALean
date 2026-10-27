module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `Alg. 1`'s loop state, linearizing at the center

`CenterAbstrState`: what one iteration of [1, Alg. 1] hands the next.

## References

* [1] [M. Wetzlinger, A. Kulmburg and M. Althoff. "Adaptive Parameter Tuning for Reachability
      Analysis of Nonlinear Systems". Proceedings of the 24th International Conference on Hybrid
      Systems: Computation and Control,
      2021.](../../../../../references/2021/wetzlinger-hscc-adaptive-tuning-nonlinear.md)
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure NonlinearSys.CenterAbstrState (S : ℕ → Type) (n : ℕ) where
  /-- `t_s`, line 15. -/
  t : ℝ
  /-- `R(t_s)`, line 12, as line 14 last reduced it. -/
  R : S n
  /-- `R(τ_s)`, line 13, as line 14 last reduced it. -/
  Rτ : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
