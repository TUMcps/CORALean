module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Restructure

@[expose] public section

/-!
# `restructure` leaves no independent generator

What the operation is for, and the half of its specification no enclosure
theorem sees: `restructure_outer` would hold of an operation that changed
nothing at all.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

@[simp] theorem PolyZonotope.restructure_q (pZ : PolyZonotope (Vec ℝ n)) :
    pZ.restructure.q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
