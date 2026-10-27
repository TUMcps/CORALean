module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
public import CORALean.ContSet.ProbZonotope.Real.Definitions.GaussPdf

@[expose] public section

/-!
# The enclosing probabilistic hull of a probabilistic zonotope

[1, Def. 4]: `f̄_𝒵 = sup{f_𝒵 | E[𝒵] ∈ Z}`, the pointwise supremum of the densities of the
G-zonotopes whose mean lies in `Z`. The density of `N(μ, Σ)` is `gaussPdf μ Σ`
(`Theorems.GZonotopeLawDensity`, for invertible `Σ`), so the hull is the supremum of
`gaussPdf μ Σ x` over `μ ∈ Z`.

## Inputs
* `P` – probabilistic zonotope
* `x` – point

## Output
* the pointwise supremum over the means `μ` of the Gaussian densities at `x`

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

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `f̄_𝒵(x) = sup_{μ ∈ Z} f_{N(μ, Σ)}(x)`. -/
noncomputable def ProbZonotope.eph (P : ProbZonotope n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun μ => gaussPdf μ P.cov x) '' P.Z.construct)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
