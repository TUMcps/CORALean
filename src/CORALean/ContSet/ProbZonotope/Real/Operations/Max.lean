module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

@[expose] public section

/-!
# `ProbZonotope.max`

CORA's `max(probZ, m)` and [1] eq. (3): the value `1 / ((2π)^{n/2} det(Σ)^{1/2}) · exp(-m²/2)`
of the Gaussian density `N(μ, Σ)` on its `m`-sigma bound `(x - μ)ᵀ Σ⁻¹ (x - μ) = m²`, the same
for every mean `μ`. `Theorems.GaussPdfLeMaxIff` says it is the largest density value outside
the `m`-sigma ellipsoid.

## Inputs
* `P` – probabilistic zonotope
* `m` – real number

## Output
* the Gaussian density `exp(-m²/2) / ((2π)^{n/2} det(Σ)^{1/2})` on the `m`-sigma bound

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open scoped _root_.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.max (P : ProbZonotope n) (m : ℝ) : ℝ :=
  1 / ((2 * π) ^ ((n : ℝ) / 2) * P.cov.det ^ ((1 : ℝ) / 2)) * Real.exp (-(1 / 2) * m ^ 2)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
