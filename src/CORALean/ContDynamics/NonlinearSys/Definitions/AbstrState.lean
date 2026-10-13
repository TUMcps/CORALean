module

public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `Alg. 1`'s loop state

`AbstrState`: what one iteration of [1, Alg. 1] hands the next.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- ========================================  MAIN TYPE  ========================================= --

/-- What one iteration of [1, Alg. 1] hands the next. -/
structure NonlinearSys.AbstrState (S : ℕ → Type) (n : ℕ) where
  /-- `t_k`, line 16. -/
  t : ℝ
  /-- `R(t_k)`, line 13, as line 15 last reduced it. -/
  R : S n
  /-- `R(τ_k)`, line 14, as line 15 last reduced it. -/
  Rτ : S n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
