module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonotopeConZonotopeExact

@[expose] public section

/-!
# Every zonotope is a halfspace description

A zonotope is the constrained zonotope with no constraint (`Zonotope.conZonotope_exact`), and the
constrained zonotopes are exactly the bounded halfspace descriptions
(`ConZonotope.exists_construct_eq_iff_hPolytope`). The description is found, not computed: a
zonotope in `n` dimensions with `l` generators has up to `2 · (l choose n-1)` facets.

This is the arrow from zonotopes to polytopes of [1, Fig. 1 (Zonotopes → Polytopes)].

## Inputs
* `Z` – zonotope

## Hypotheses
* none

## Conclusion
* some halfspace polytope equals the zonotope

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.

-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.exists_hPolytope_exact (Z : Zonotope (Vec ℝ n)) :
    ∃ P : HPolytope (Vec ℝ n), P.construct = Z.construct := by
  obtain ⟨P, hP, -⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mp
    ⟨Z.conZonotope, (Zonotope.conZonotope_exact Z).symm⟩
  exact ⟨P, hP⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
