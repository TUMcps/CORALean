import CORALean.ContSet.ConPolyZono.Real.Operations.Plus

/-!
# `ConPolyZono.plus`'s counts

`plus` is `PolyZonotope.plus` with the two constraint systems carried along
side by side: all five counts concatenate, since nothing couples the two sets
and nothing may be identified. `rfl` against the structure instance in
`Operations/Plus.lean`.
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
theorem ConPolyZono.plus_p (C₁ C₂ : ConPolyZono α) : (C₁.plus C₂).p = C₁.p + C₂.p := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_h (C₁ C₂ : ConPolyZono α) : (C₁.plus C₂).h = C₁.h + C₂.h := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_q (C₁ C₂ : ConPolyZono α) : (C₁.plus C₂).q = C₁.q + C₂.q := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_m (C₁ C₂ : ConPolyZono α) : (C₁.plus C₂).m = C₁.m + C₂.m := rfl

omit [Module ℝ α] in
theorem ConPolyZono.plus_s (C₁ C₂ : ConPolyZono α) : (C₁.plus C₂).s = C₁.s + C₂.s := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
