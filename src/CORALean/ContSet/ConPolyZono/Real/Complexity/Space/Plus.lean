module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

@[expose] public section

/-!
# `ConPolyZono.plus`'s counts

`plus` is `PolyZonotope.plus` with the two constraint systems carried along
side by side: all five counts concatenate, since nothing couples the two sets
and nothing may be identified. `rfl` against the structure instance in
`Operations/Plus.lean`.
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
theorem ConPolyZono.plus_p (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).p = cPZ₁.p + cPZ₂.p := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_h (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).h = cPZ₁.h + cPZ₂.h := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_q (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).q = cPZ₁.q + cPZ₂.q := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_m (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).m = cPZ₁.m + cPZ₂.m := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_s (cPZ₁ cPZ₂ : ConPolyZono α) : (cPZ₁.plus cPZ₂).s = cPZ₁.s + cPZ₂.s := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
