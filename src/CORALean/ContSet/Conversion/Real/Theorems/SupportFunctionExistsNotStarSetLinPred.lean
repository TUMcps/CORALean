module

public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidExistsNotStarSetLinPred
public import CORALean.ContSet.Conversion.Real.Theorems.EllipsoidSupportFunctionExact

@[expose] public section

/-!
# A support function that is no star set of CORA's predicate

The ellipsoid's closed-form support function denotes the unit disc
(`Ellipsoid.supportFunction_exact`), which is no star set with CORA's linear predicate
(`Ellipsoid.exists_not_starSet_linPred`). So the arrow of
[1, Fig. 1 (Support Functions → Star Sets)] needs a predicate beyond the linear one: with the
support function itself as the predicate it holds (`SupportFunction.starSet_exact`).

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

theorem SupportFunction.exists_not_starSet_linPred :
    ∃ S : SupportFunction (Vec ℝ 2),
      ¬ ∃ s : StarSet StarSet.LinPred 2, s.construct = S.construct := by
  obtain ⟨E, hE⟩ := Ellipsoid.exists_not_starSet_linPred
  exact ⟨E.supportFunction, fun ⟨s, hs⟩ => hE ⟨s, hs.trans E.supportFunction_exact⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
