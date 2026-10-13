module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Resolve
public import CORALean.ContSet.PolyZonotope.Real.Theorems.GetSubsetPoint

@[expose] public section

/-!
# `PolyZonotope.resolve`'s point

At any factor vector, the resolved set's point is the original's with factor `k` replaced by the
value `x`: the factor's own value no longer matters.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.resolve_point (pZ : PolyZonotope α) (k : Fin pZ.p) (x : ℝ)
    (b : Fin pZ.p → ℝ) :
    (pZ.resolve k x).point b = pZ.point (Function.update b k x) := by
  -- `getSubset` at radius `0` substitutes the value
  unfold PolyZonotope.resolve
  rw [PolyZonotope.getSubset_point, zero_mul, add_zero]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
