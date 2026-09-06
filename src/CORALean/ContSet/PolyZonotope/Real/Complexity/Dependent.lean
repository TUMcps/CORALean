import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

/-!
# `PolyZonotope.dependent`'s counts

Every independent generator made dependent: the factor and dependent-generator
counts both grow by the independent count, and the independent block empties.
`rfl` against the structure instance in `Operations/Dependent.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_p (PZ : PolyZonotope α) :
    (PolyZonotope.dependent PZ).p = PZ.p + PZ.q := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_h (PZ : PolyZonotope α) :
    (PolyZonotope.dependent PZ).h = PZ.h + PZ.q := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_q (PZ : PolyZonotope α) : (PolyZonotope.dependent PZ).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
