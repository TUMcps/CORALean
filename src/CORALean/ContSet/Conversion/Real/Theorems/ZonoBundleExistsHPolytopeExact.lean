module

public import CORALean.ContSet.ConZonotope.Real.Theorems.ExistsConstructEqIffHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.ZonoBundleConZonotopeAllExact

@[expose] public section

/-!
# Every zonotope bundle is a halfspace description

A bundle of at least one zonotope is the constrained zonotope its members intersect to
(`ZonoBundle.conZonotopeAll_exact`), and the constrained zonotopes are exactly the bounded halfspace
descriptions (`ConZonotope.exists_construct_eq_iff_hPolytope`). An empty bundle denotes the whole
space, which is no polytope, hence the hypothesis.

This is the equivalence of polytopes and zonotope bundles of
[1, Fig. 1 (Polytopes ↔ Zonotope Bundles)].

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

theorem ZonoBundle.exists_hPolytope_exact (zB : ZonoBundle (Vec ℝ n)) (hk : 0 < zB.k) :
    ∃ P : HPolytope (Vec ℝ n), P.construct = zB.construct := by
  obtain ⟨P, hP, -⟩ := ConZonotope.exists_construct_eq_iff_hPolytope.mp
    ⟨zB.conZonotopeAll hk, ZonoBundle.conZonotopeAll_exact zB hk⟩
  exact ⟨P, hP⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
