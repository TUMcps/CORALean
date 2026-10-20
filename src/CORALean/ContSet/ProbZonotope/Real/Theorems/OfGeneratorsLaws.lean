module

public import CORALean.ContSet.ProbZonotope.Real.Operations.OfGenerators
public import CORALean.ContSet.ProbZonotope.Real.Theorems.GZonotopeLawEq

@[expose] public section

/-!
# The laws of `ofGenerators` are those of `μ + g N`

[1, Def. 4]'s G-zonotope with uncertain mean `Z ⊞ (0, g)`: its laws are exactly the laws of
the G-zonotopes `μ + g N` with certain mean `μ ∈ Z` (`gZonotopeLaw_eq`).

## Inputs
* `Z` – zonotope
* `g` – `n × q` matrix

## Hypotheses
* none

## Conclusion
* the laws of `ofGenerators` are those of `μ + g N`

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem ProbZonotope.ofGenerators_laws (Z : Zonotope (Vec ℝ n)) (g : Mat ℝ n q) :
    (ProbZonotope.ofGenerators Z g).laws = {m | ∃ μ ∈ Z.construct, m = gZonotopeLaw μ g} := by
  ext m
  simp only [ProbZonotope.laws, ProbZonotope.ofGenerators, Set.mem_setOf_eq, gZonotopeLaw_eq]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
