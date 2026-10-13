module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Operations.Shift

@[expose] public section

/-!
# `shift`'s point is the point moved

The centre is the first summand of `point`, so the translation comes straight
back out; `add_right_comm` is the whole argument.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.shift_point (pZ : PolyZonotope α) (v : α) (a : Fin pZ.p → ℝ) :
    (pZ.shift v).point a = pZ.point a + v := by
  show pZ.c + v + ∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i
      = pZ.c + (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i) + v
  exact add_right_comm _ _ _

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
