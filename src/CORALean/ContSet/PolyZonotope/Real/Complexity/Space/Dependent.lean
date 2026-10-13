module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent

@[expose] public section

/-!
# `PolyZonotope.dependent`'s counts

Every independent generator made dependent: the factor and dependent-generator
counts both grow by the independent count, and the independent block empties.
`rfl` against the structure instance in `Operations/Dependent.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_p (pZ : PolyZonotope α) :
    (PolyZonotope.dependent pZ).p = pZ.p + pZ.q := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_h (pZ : PolyZonotope α) :
    (PolyZonotope.dependent pZ).h = pZ.h + pZ.q := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.dependent_q (pZ : PolyZonotope α) : (PolyZonotope.dependent pZ).q = 0 := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
