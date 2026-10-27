module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MergePoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortPoint

@[expose] public section

/-!
# `sortPlus`'s point is the sum of the two points

[1, Prop. 3.4] at one factor vector: neither `sort` nor `merge` moves a point,
so what is left is `exactPlus_point`, and the same reading applies — this is
the sum of the two sets' points at one factor vector, not the Minkowski sum.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the sum of the two points

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
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
