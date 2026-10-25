module

public import CORALean.Global.Tensor
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# G-zonotopes with certain mean

[1, Def. 3]: replacing the coefficients `β⁽ⁱ⁾ ∈ [-1, 1]` of a zonotope by independent standard
Gaussian variables gives the random vector `c + Σᵢ N⁽ⁱ⁾(0, 1) g⁽ⁱ⁾ = c + G N`. Its law is the
standard Gaussian on `ℝ^q` pushed through `β ↦ c + Gβ`, here on Euclidean space, where
Mathlib's `stdGaussian` lives: `toLp` and `ofLp` cross between it and `Vec ℝ n`.

## Inputs
* `c` – center of length `n`
* `G` – `n × q` matrix

## Output
* the law of `c + G N`, `N` standard Gaussian on `ℝ^q`

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open MeasureTheory ProbabilityTheory WithLp Matrix

variable {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The law of `c + G N`, `N` standard Gaussian on `ℝ^q`. -/
noncomputable def gZonotopeLaw (c : Vec ℝ n) (G : Mat ℝ n q) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin q))).map (fun β => toLp 2 (c + G *ᵥ ofLp β))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
