module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
public import CORALean.ContSet.ProbZonotope.Real.Operations.ConfidenceZonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ProbZonotope.zonotope`

CORA's `zonotope(probZ, m)` and [1, Sec. V]'s confidence set of a G-zonotope with uncertain
mean, `η(𝒵, m) = Z + η(𝒵̲, m)`: the mean zonotope plus `m` times `n` probabilistic generators
`g` with `g gᵀ = Σ`. CORA takes them from an eigendecomposition of `Σ` (`probReduce`); any
`g` with `g gᵀ = Σ` spans the same Gaussian, and the symmetric square root of `Σ` is used here.
`Theorems.ZonotopeProb` is its probability.

## Inputs
* `P` – probabilistic zonotope
* `m` – real number

## Output
* the confidence zonotope: the mean zonotope plus `m` times the generators of `Σ`

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems using
      Enclosing Hulls of Probability Density Functions". 2009 European Control Conference (ECC),
      2009.](../../../../../../references/2009/althoff-ecc-enclosing-hulls.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open scoped MatrixOrder

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def ProbZonotope.zonotope (P : ProbZonotope n) (m : ℝ) : Zonotope (Vec ℝ n) :=
  P.Z.plus (confidenceZonotope (CFC.sqrt P.cov) m)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
