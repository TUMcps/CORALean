module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PadFront

@[expose] public section

/-!
# `PolyZonotope.padFront`'s counts

`l` fresh factors before the set's own; the dependent and independent
generator counts stand, since only the factor count and the exponent matrix
move. `rfl` against the structure instance in `Operations/PadFront.lean`.
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
theorem PolyZonotope.padFront_p (l : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padFront l pZ).p = l + pZ.p := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padFront_h (l : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padFront l pZ).h = pZ.h := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padFront_q (l : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padFront l pZ).q = pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
