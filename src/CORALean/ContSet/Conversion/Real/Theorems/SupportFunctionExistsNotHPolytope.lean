module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotHPolytope
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSupportFunctionExact

@[expose] public section

/-!
# A support function that is no polytope

A polytope is a support function (`HPolytope.supportFunction_exact`), and the inclusion is strict:
the ellipsoid's closed-form support function denotes the unit disc
(`Ellipsoid.supportFunction_exact`), which is no halfspace description
(`Ellipsoid.exists_not_hPolytope`).

This is the arrow from polytopes to support functions of
[1, Fig. 1 (Polytopes → Support Functions)].

## Inputs
* none

## Hypotheses
* none

## Conclusion
* some planar support function is no halfspace polytope

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

theorem SupportFunction.exists_not_hPolytope :
    ∃ S : SupportFunction (Vec ℝ 2), ¬ ∃ P : HPolytope (Vec ℝ 2), P.construct = S.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_hPolytope
  exact ⟨E.supportFunction, fun ⟨P, hP⟩ => hE ⟨P, hP.trans E.supportFunction_exact⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
