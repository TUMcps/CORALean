import CORALean.ContSet.ConPolyZono.Real.Operations.Map

/-!
# `ConPolyZono.map` leaves the constraint untouched
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constraint is untouched, and `rfl` is the honest proof of it. -/
theorem ConPolyZono.satisfies_map (f : α →ₗ[ℝ] β) (C : ConPolyZono α)
    (a : Fin C.p → ℝ) : (C.map f).satisfies a ↔ C.satisfies a := Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
