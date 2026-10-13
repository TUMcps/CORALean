module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope
public import CORALean.ContSet.Zonotope.Real.Operations.Mtimes

@[expose] public section

/-!
# `ProbZonotope.mtimes`

CORA's `mtimes` by a matrix (its numeric branch) and [1, Eq. 4]'s linear map
`L Z₁ = (L c, L g⁽¹…ᵖ⁾, L Σ₁ Lᵀ)`. CORA's interval-matrix branch, which [1] does not state, is not
modelled. `Theorems.MtimesLaws` says what it means for the laws.

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

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.mtimes (M : Mat ℝ m n) (P : ProbZonotope n) : ProbZonotope m :=
  ⟨Zonotope.mtimes M P.Z, M * P.cov * M.transpose⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
