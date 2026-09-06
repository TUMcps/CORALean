import CORALean.ContSet.PolyZonotope.Real.Operations.SubsetAt
import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint

/-!
# `map` carries a factor sub-box to the corresponding subset

[1]'s dependency result, composed: `map_point` says one factor vector names
corresponding points before and after `map`, so a sub-box `B` of the *initial*
factor domain names the corresponding subset of every later set in a chain —
`bilin_point` and `gcnSteps_point` are the same pattern at a pairing and at a
recursion.

`map` preserves `p` definitionally, so `B` needs no transport here; that is
what keeps this instance free of a `Fin.cast`, unlike a chain through `bilin`
or `padFront`.

## References

* [1] N. Kochdumper, B. Schürmann and M. Althoff. "Utilizing Dependencies to
      Obtain Subsets of Reachable Sets". HSCC 2020. arXiv:1910.08354.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- `map`'s subset at `B` is `f`'s image of the original subset at `B`. -/
theorem PolyZonotope.map_subsetAt (f : α →ₗ[ℝ] β) (S : PolyZonotope α)
    (B : Set (Fin S.p → ℝ)) : (S.map f).subsetAt B = f '' S.subsetAt B := by
  show (S.map f).point '' B = f '' (S.point '' B)
  rw [← Set.image_comp]
  exact Set.image_congr fun a _ => PolyZonotope.map_point f S a

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
