module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotStarSetHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSupportFunctionExact

@[expose] public section

/-!
# A support function that is no star set of CORA's predicate

The ellipsoid's closed-form support function denotes the unit disc
(`Ellipsoid.supportFunction_exact`), which is no star set with CORA's linear predicate
(`Ellipsoid.exists_not_starSet_hPolytope`). So the arrow of
[1, Fig. 1 (Support Functions → Star Sets)] needs a predicate beyond the linear one: with the
support function itself as the predicate it holds, on a box around the disc
(`SupportFunction.starSet_exact`).

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some planar support function is no star set with polytope predicate

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- The unit disc's support function is no star set with a polytope predicate. -/
theorem SupportFunction.exists_not_starSet_hPolytope :
    ∃ S : SupportFunction (Vec ℝ 2),
      ¬ ∃ s : StarSet ℋ𝒫 2, s.construct = S.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_starSet_hPolytope
  exact ⟨E.supportFunction, fun ⟨s, hs⟩ => hE ⟨s, hs.trans E.supportFunction_exact⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
