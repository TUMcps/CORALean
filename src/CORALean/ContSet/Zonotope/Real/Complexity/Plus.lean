import CORALean.ContSet.Zonotope.Real.Operations.Plus

/-!
# `Zonotope.plus_h`

`plus`'s generator count: the two operands' concatenated, with nothing
absorbed and nothing bounded. `rfl`, since `Operations/Plus.lean` states `h`
directly in the structure instance.
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
theorem Zonotope.plus_h (Z₁ Z₂ : Zonotope α) : (Z₁.plus Z₂).h = Z₁.h + Z₂.h := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
