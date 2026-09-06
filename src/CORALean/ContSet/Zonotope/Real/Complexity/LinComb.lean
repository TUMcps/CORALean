import CORALean.ContSet.Zonotope.Real.Operations.LinComb

/-!
# `Zonotope.linComb_h`

`linComb`'s generator count: the two operands' plus the one fresh generator
that ties them together at the interpolating point. `rfl`, since
`Operations/LinComb.lean` states `h` directly in the structure instance.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.linComb_h (Z₁ Z₂ : Zonotope α) : (Z₁.linComb Z₂).h = Z₁.h + Z₂.h + 1 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
