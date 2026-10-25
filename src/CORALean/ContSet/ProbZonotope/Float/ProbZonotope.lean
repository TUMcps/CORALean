module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

@[expose] public section

/-!
# Probabilistic zonotopes over a floating-point scalar: the representation

CORA's `probZonotope` with a float zonotope of possible means and the covariance as an interval
matrix, which holds the true covariance through the rounding of the operations that built it. What
it stands for is the family of Gaussian laws `N(μ, Σ)`, one for each `μ` in the mean zonotope and
each positive semidefinite `Σ` in the covariance interval. The operations' theorems are outer:
every law the real operation produces from laws of the operands is a law of the result.
The set of means and the covariance are [1, Def. 4]'s G-zonotope with uncertain mean, which
CORA's `probZonotope` implements.
There is no `I_error` and no `absorbRounding`: the rounding sits in the means' box and covariance.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open MeasureTheory ProbabilityTheory WithLp FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A probabilistic zonotope over floats: the zonotope `Z` and the covariance `cov` as an interval
matrix. -/
structure ProbZonotope (𝕋 : Type) (n : ℕ) where
  Z : Zonotope (Vec 𝕋 n)
  cov : Interval (Mat 𝕋 n n)

/-- The Gaussian laws `N(μ, Σ)` with `μ` in the mean zonotope and `Σ` a positive semidefinite
matrix in the covariance interval. -/
def ProbZonotope.laws [SoundFloatArithmetic 𝕋] (P : ProbZonotope 𝕋 n) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {m | ∃ μ ∈ P.Z.construct, ∃ S ∈ P.cov.construct,
    S.PosSemidef ∧ m = multivariateGaussian (toLp 2 μ) S}

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
