import CORALean.ContSet.ConZonotope.Real.Operations.Plus

/-!
# `ConZonotope.plus`'s counts

`plus`'s generator count: the two operands' concatenated, exactly as a
zonotope's would. The constraint counts add too — `comap` leaves a row list
untouched and `intersection` concatenates it, so pulling each operand's polytope back
onto its own block and intersecting costs nothing beyond what each already
had. `rfl` against the structure instance in `Operations/Plus.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ConZonotope.plus_h (cZ₁ cZ₂ : ConZonotope α) : (cZ₁.plus cZ₂).h = cZ₁.h + cZ₂.h := rfl

omit [Module ℝ α] in
theorem ConZonotope.plus_P_m (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.plus cZ₂).P.m = cZ₁.P.m + cZ₂.P.m := rfl

omit [Module ℝ α] in
theorem ConZonotope.plus_P_me (cZ₁ cZ₂ : ConZonotope α) :
    (cZ₁.plus cZ₂).P.me = cZ₁.P.me + cZ₂.P.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
