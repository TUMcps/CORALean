module

public import CORALean.ContSet.ProbZonotope.Real.ProbZonotope

@[expose] public section

/-!
# `ProbZonotope.ofGenerators`

CORA's constructor `probZonotope(Z, g)` with its `sigma`: from the mean zonotope `Z` and the
probabilistic generators `g⁽¹…ᑫ⁾`, the covariance `Σ = g gᵀ`. [1, Def. 4] builds the
G-zonotope with uncertain mean `Z ⊞ (0, g⁽¹…ᑫ⁾)` the same way. `Theorems.OfGeneratorsLaws` reads
its laws as those of `μ + g N`, `μ ∈ Z`.

## Inputs
* `Z` – zonotope
* `g` – `n × q` matrix

## Output
* the probabilistic zonotope with mean zonotope `Z` and covariance `g gᵀ`

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

variable {n q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ProbZonotope.ofGenerators (Z : Zonotope (Vec ℝ n)) (g : Mat ℝ n q) : ProbZonotope n :=
  ⟨Z, g * g.transpose⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
