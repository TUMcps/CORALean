import CORALean.ContSet.ConZonotope.Real.Operations.Plus

/-!
# `ConZonotope.plus`'s counts

`plus`'s generator count: the two operands' concatenated, exactly as a
zonotope's would. The constraint counts add too — `comap` leaves a row list
untouched and `and` concatenates it, so pulling each operand's polytope back
onto its own block and intersecting costs nothing beyond what each already
had. `rfl` against the structure instance in `Operations/Plus.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ConZonotope.plus_h (C₁ C₂ : ConZonotope α) : (C₁.plus C₂).h = C₁.h + C₂.h := rfl

omit [Module ℝ α] in
theorem ConZonotope.plus_P_m (C₁ C₂ : ConZonotope α) : (C₁.plus C₂).P.m = C₁.P.m + C₂.P.m := rfl

omit [Module ℝ α] in
theorem ConZonotope.plus_P_me (C₁ C₂ : ConZonotope α) :
    (C₁.plus C₂).P.me = C₁.P.me + C₂.P.me := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
