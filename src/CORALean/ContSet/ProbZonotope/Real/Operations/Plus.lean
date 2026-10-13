module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# `ProbZonotope.plus`

CORA's `plus` of two probabilistic zonotopes and [1, Eq. 4]'s sum
`Z₁ + Z₂ = (c₁ + c₂, g⁽¹…ᵖ⁾, h⁽¹…ᑫ⁾, Σ₁ + Σ₂)`: the mean zonotopes are added as zonotopes, the
covariances as matrices. `Theorems.PlusLaws` says what it means for the laws.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Safety Assessment for Stochastic Linear Systems
      using Enclosing Hulls of Probability Density Functions". In Proc. of the European Control
      Conference (ECC), pp. 625-630, 2009.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.plus (P₁ P₂ : ProbZonotope n) : ProbZonotope n :=
  ⟨P₁.Z.plus P₂.Z, P₁.cov + P₂.cov⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
