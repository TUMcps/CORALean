module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

@[expose] public section

/-!
# `PolyZonotope.plus`'s counts

`plus`'s three counts: factors, dependent generators and independent
generators all concatenate, since the two exponent matrices are laid out
block-diagonally rather than identified. `rfl` against the structure instance
in `Operations/Plus.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- The `p` count of `plus`'s result. -/
theorem PolyZonotope.plus_p (pZ₁ pZ₂ : PolyZonotope α) : (pZ₁.plus pZ₂).p = pZ₁.p + pZ₂.p := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
