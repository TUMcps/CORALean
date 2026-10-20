module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Stack
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ExactPlusPoint
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MapPoint
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point

@[expose] public section

/-!
# `PolyZonotope.stack`'s point

At one factor vector, the two sets' points stacked: the first `n₁` coordinates are the first
set's point, the last `n₂` the second's. Stated at the point, as `exactPlus_point` is, and not at
the set: the factors are shared, so a set-level statement would need the pairing of values.

## Inputs
* `pZ₁` – first polynomial zonotope
* `pZ₂` – second polynomial zonotope
* `a` – factor values

## Hypotheses
* `hp` – both have the same factor count

## Conclusion
* the point is the concatenation of the two points
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open CORALean

variable {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.stack_point (pZ₁ : PolyZonotope (Vec ℝ n₁)) (pZ₂ : PolyZonotope (Vec ℝ n₂))
    (hp : pZ₁.p = pZ₂.p) (a : Fin pZ₁.p → ℝ) : -- --- CONCL ---
    (pZ₁.stack pZ₂ hp).point a =
      (Fin.append (pZ₁.point a) (pZ₂.point (fun k => a (Fin.cast hp.symm k))) :
        Vec ℝ (n₁ + n₂)) := by -- --- PROOF ---
  unfold PolyZonotope.stack
  rw [PolyZonotope.exactPlus_point, PolyZonotope.map_point, PolyZonotope.map_point]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [blockPadLeft, blockPadRight]
  rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
