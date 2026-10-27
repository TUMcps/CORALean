module

public import CORALean.ContSet.Zonotope.Real.Zonotope
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Probabilistic zonotopes: the representation

CORA's `probZonotope` and [1, Def. 4]'s G-zonotope with uncertain mean, in the form
`(c, g⁽¹…ᵖ⁾, Σ)`: a zonotope `Z` of possible means and a covariance matrix `Σ`. It is neither a
set nor a random vector; what it stands for is the family of Gaussian laws `N(μ, Σ)`, one for
every `μ ∈ Z` — `laws`, as measures on Euclidean space. CORA also stores the probabilistic
generators `g` with `Σ = g gᵀ` (`sigma`) and the cut-off `γ` of its confidence sets; `Σ` is
all the laws need, `ofGenerators` is CORA's constructor from `g`, and `γ` is an argument of
the confidence-set operation instead. Real layer only.

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp

variable {n : ℕ}


-- ========================================  MAIN TYPE  ========================================= --

/-- A probabilistic zonotope: the zonotope `Z` and the covariance matrix `cov`. -/
structure ProbZonotope (n : ℕ) where
  Z : Zonotope (Vec ℝ n)
  cov : Mat ℝ n n

/-- The Gaussian laws `N(μ, Σ)` with `μ ∈ Z`: what `E[𝒵] ∈ Z` ranges over in [1, Def. 4]. -/
noncomputable def ProbZonotope.laws (P : ProbZonotope n) :
    Set (Measure (EuclideanSpace ℝ (Fin n))) :=
  {m | ∃ μ ∈ P.Z.construct, m = multivariateGaussian (toLp 2 μ) P.cov}

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
