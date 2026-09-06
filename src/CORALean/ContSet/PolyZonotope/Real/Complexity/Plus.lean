import CORALean.ContSet.PolyZonotope.Real.Operations.Plus

/-!
# `PolyZonotope.plus`'s counts

`plus`'s three counts: factors, dependent generators and independent
generators all concatenate, since the two exponent matrices are laid out
block-diagonally rather than identified. `rfl` against the structure instance
in `Operations/Plus.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem PolyZonotope.plus_p (PZ₁ PZ₂ : PolyZonotope α) : (PZ₁.plus PZ₂).p = PZ₁.p + PZ₂.p := rfl

omit [Module ℝ α] in
theorem PolyZonotope.plus_h (PZ₁ PZ₂ : PolyZonotope α) : (PZ₁.plus PZ₂).h = PZ₁.h + PZ₂.h := rfl

omit [Module ℝ α] in
theorem PolyZonotope.plus_q (PZ₁ PZ₂ : PolyZonotope α) : (PZ₁.plus PZ₂).q = PZ₁.q + PZ₂.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
