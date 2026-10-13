import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.MergePoint
import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPoint

/-!
# `sortPlus`'s point is the sum of the two points

[1, Prop. 3.4] at one factor vector: neither `sort` nor `merge` moves a point,
so what is left is `exactPlus_point`, and the same reading applies — this is
the sum of the two sets' points at one factor vector, not the Minkowski sum.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sortPlus_point (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p)
    (a : Fin pZ₁.p → ℝ) :
    (pZ₁.sortPlus pZ₂ hp).point a
      = pZ₁.point a + pZ₂.point (fun k => a (Fin.cast hp.symm k)) := by
  show ((pZ₁.exactPlus pZ₂ hp).sort.merge).point a = _
  rw [PolyZonotope.merge_point, PolyZonotope.sort_point, PolyZonotope.exactPlus_point]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
