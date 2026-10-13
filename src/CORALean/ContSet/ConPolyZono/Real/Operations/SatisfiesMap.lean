module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Map

@[expose] public section

/-!
# `ConPolyZono.map` leaves the constraint untouched
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α β : Type} [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constraint is untouched, and `rfl` is the honest proof of it. -/
theorem ConPolyZono.satisfies_map (f : α →ₗ[ℝ] β) (cPZ : ConPolyZono α)
    (a : Fin cPZ.p → ℝ) : (cPZ.map f).satisfies a ↔ cPZ.satisfies a := Iff.rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
