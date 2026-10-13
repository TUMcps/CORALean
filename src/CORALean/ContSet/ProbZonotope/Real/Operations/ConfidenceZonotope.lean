module

public import CORALean.ContSet.Zonotope.Real.Zonotope

@[expose] public section

/-!
# The confidence set operator

[1, Prop. 2, eq. (5)]: `η(𝒵, m) = (0, g⁽¹…ⁿ⁾)`, `g⁽ⁱ⁾ = m · g̲⁽ⁱ⁾` — a zero-mean G-zonotope with
`n` probabilistic generators, the columns of `G`, turned into the zonotope whose generators
are `m` times them. `Theorems.ConfidenceZonotopeProb` is its probability.

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

def confidenceZonotope (G : Mat ℝ n n) (m : ℝ) : Zonotope (Vec ℝ n) :=
  ⟨n, 0, fun i => m • fun j => G j i⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
