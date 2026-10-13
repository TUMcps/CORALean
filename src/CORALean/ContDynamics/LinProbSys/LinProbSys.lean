module

public import CORALean.ContDynamics.LinearSys.Definitions.NoiseCovariance

@[expose] public section

/-!
# Linear systems with white noise: the representation

CORA's `linProbSys` [1], the multivariate Ornstein-Uhlenbeck process
`ẋ(t) = A x(t) + B u(t) + C ξ(t)` with white Gaussian noise `ξ`. Real layer only: the noise
is a Gaussian process, with no float counterpart. `C` is square, as CORA's `inputArgsCheck`
asks. The system is the three matrices; what it denotes is the law of its solution, a Gaussian
whose noise part has the covariance `noiseCovariance A C t`, which `noiseCovariance_add`
reads on two steps. The stochastic process itself is not defined here.

## References

* [1] `contDynamics/@linProbSys/linProbSys.m`
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure LinProbSys (n m : ℕ) where
  A : Mat ℝ n n
  B : Mat ℝ n m
  C : Mat ℝ n n

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
