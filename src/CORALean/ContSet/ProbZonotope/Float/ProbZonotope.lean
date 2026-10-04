import CORALean.ContSet.Zonotope.Float.Zonotope
import CORALean.ContSet.Interval.Float.Interval
import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

/-!
# Probabilistic zonotopes over a floating-point scalar: the representation

CORA's `probZonotope` with a float zonotope of possible means and the covariance as an interval
matrix, which holds the true covariance through the rounding of the operations that built it. What
it stands for is the family of Gaussian laws `N(μ, Σ)`, one for each `μ` in the mean zonotope and
each positive semidefinite `Σ` in the covariance interval. The operations' theorems are outer:
every law the real operation produces from laws of the operands is a law of the result.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory WithLp FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

structure ProbZonotope (𝕋 : Type) (n : ℕ) where
  Z : Zonotope 𝕋 n
  cov : Interval (Mat 𝕋 n n)

/-- The Gaussian laws `N(μ, Σ)` with `μ` in the mean zonotope and `Σ` a positive semidefinite
matrix in the covariance interval. -/
def ProbZonotope.laws [SoundFloatArithmetic 𝕋] (P : ProbZonotope 𝕋 n) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {m | ∃ μ ∈ P.Z.construct, ∃ S ∈ P.cov.construct,
    S.PosSemidef ∧ m = multivariateGaussian (toLp 2 μ) S}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
