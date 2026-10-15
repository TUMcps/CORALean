module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotStarSet
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSupportFunctionExact

@[expose] public section

/-!
# A support function that is no star set

The ellipsoid's closed-form support function denotes the unit disc
(`Ellipsoid.supportFunction_exact`), which is no star set with a linear predicate
(`Ellipsoid.exists_not_starSet`). So the arrow of Fig. 1 of Kochdumper and Althoff (TAC 2021) from
support functions to star sets holds of star sets whose predicate may be nonlinear, and not of
`StarSet`.

This is the arrow from support functions to star sets of
[1, Fig. 1 (Support Functions → Star Sets)].

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


-- =======================================  MAIN THEOREM  ======================================= --

theorem SupportFunction.exists_not_starSet :
    ∃ S : SupportFunction (Vec ℝ 2), ¬ ∃ s : StarSet 2, s.construct = S.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_starSet
  exact ⟨E.supportFunction, fun ⟨s, hs⟩ => hE ⟨s, hs.trans E.supportFunction_exact⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
