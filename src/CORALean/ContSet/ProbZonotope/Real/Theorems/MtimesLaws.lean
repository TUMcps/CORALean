module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.MapMultivariateGaussian
public import CORALean.ContSet.ProbZonotope.Real.Operations.Mtimes
public import CORALean.ContSet.Zonotope.Real.Theorems.MtimesExact

@[expose] public section

/-!
# `ProbZonotope.mtimes` maps the laws

[1, Eq. 4]'s linear map: the images of the laws of `P` under `x ↦ Lx` are exactly the laws
of `L P`. The image of `N(a, Σ)` is `N(La, LΣLᵀ)`, by characteristic functions
(`⟨Lx, t⟩ = ⟨x, Lᵀt⟩`), and the means range over `L Z` (`Zonotope.mtimes_exact`). The
covariance must be positive semidefinite.

## Inputs
* `M` – `m × n` matrix
* `P` – probabilistic zonotope

## Hypotheses
* `h` – `P.cov` is positive semidefinite

## Conclusion
* the images of the laws of `P` under `M` are the laws of `P.mtimes M`

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

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open scoped RealInnerProductSpace

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.mtimes_laws (M : Mat ℝ m n) (P : ProbZonotope n)
    (h : P.cov.PosSemidef) : -- --- CONCL ---
    (fun μ => μ.map (fun x => toLp 2 (M *ᵥ ofLp x))) '' P.laws
      = (P.mtimes M).laws := by -- --- PROOF ---
  ext ν
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨M *ᵥ a, ?_, ?_⟩
    · rw [ProbZonotope.mtimes, ← Zonotope.mtimes_exact]
      exact ⟨a, ha, rfl⟩
    · beta_reduce
      rw [map_multivariateGaussian M _ h, WithLp.ofLp_toLp]
      rfl
  · rintro ⟨μ, hμ, rfl⟩
    rw [ProbZonotope.mtimes, ← Zonotope.mtimes_exact] at hμ
    obtain ⟨a, ha, rfl⟩ := hμ
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    beta_reduce
    rw [map_multivariateGaussian M _ h, WithLp.ofLp_toLp]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
