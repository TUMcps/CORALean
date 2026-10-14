module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure
public import CORALean.ContSet.PolyZonotope.Real.Theorems.DifferentiablePoint

@[expose] public section

/-!
# `ContSet/PolyZonotope/Real/Theorems`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- =============================  `PolyZonotope.continuous_point`  ============================== --
-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- The point map is continuous -/
theorem PolyZonotope.continuous_point (pZ : PolyZonotope (Vec ℝ n)) :
    Continuous pZ.point :=
  (PolyZonotope.differentiable_point pZ).continuous

end CORALean.Real


-- ===============================  `PolyZonotope.restructure_q`  =============================== --
-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean.Real

variable {n : ℕ}

/-- What the operation is for, and the half of its specification no enclosure
theorem sees: `restructure_outer` would hold of an operation that changed
nothing at all. -/
@[simp] theorem PolyZonotope.restructure_q (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.restructure.q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
