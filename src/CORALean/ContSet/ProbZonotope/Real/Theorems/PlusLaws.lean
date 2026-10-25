module

public import CORALean.ContSet.ProbZonotope.Real.Theorems.ConvMultivariateGaussian
public import CORALean.ContSet.ProbZonotope.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Theorems.PlusExact

@[expose] public section

/-!
# `ProbZonotope.plus` adds the laws

[1, Eq. 4]'s sum, read as the sum of independent random vectors, one from each family: the
laws of `X₁ + X₂`, convolutions `μ₁ ∗ μ₂` with `μᵢ` a law of `Pᵢ`, are exactly the laws of
`P₁ + P₂`. A convolution of Gaussians `N(a, Σ₁) ∗ N(b, Σ₂)` is `N(a + b, Σ₁ + Σ₂)` — the
"addition rule of random variables with Gaussian distribution" [1] applies, by characteristic
functions — and the means range over `Z₁ ⊕ Z₂` (`Zonotope.plus_exact`). The covariances must
be positive semidefinite, as a covariance is; [1] leaves the independence implicit.

## Inputs
* `P₁` – probabilistic zonotope
* `P₂` – probabilistic zonotope

## Hypotheses
* `h₁` – `P₁.cov` is positive semidefinite
* `h₂` – `P₂.cov` is positive semidefinite

## Conclusion
* the convolutions of laws of `P₁` and `P₂` are the laws of the sum

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

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.plus_laws (P₁ P₂ : ProbZonotope n) (h₁ : P₁.cov.PosSemidef)
    (h₂ : P₂.cov.PosSemidef) : -- --- CONCL ---
    Set.image2 (· ∗ ·) P₁.laws P₂.laws = (P₁.plus P₂).laws := by -- --- PROOF ---
  ext m
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨a + b, ?_, ?_⟩
    · rw [ProbZonotope.plus, ← Zonotope.plus_exact]
      exact Set.add_mem_add ha hb
    · beta_reduce
      rw [conv_multivariateGaussian _ _ h₁ h₂, ← WithLp.toLp_add]
      rfl
  · rintro ⟨μ, hμ, rfl⟩
    rw [ProbZonotope.plus, ← Zonotope.plus_exact] at hμ
    obtain ⟨a, ha, b, hb, rfl⟩ := hμ
    refine ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, ?_⟩
    beta_reduce
    rw [conv_multivariateGaussian _ _ h₁ h₂, ← WithLp.toLp_add]
    rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
