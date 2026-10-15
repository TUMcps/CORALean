module

public import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack

@[expose] public section

/-!
# `PolyZonotope.padBack`'s counts

`r` fresh factors after the set's own; the dependent and independent generator
counts stand, since only the factor count and the exponent matrix move. `rfl`
against the structure instance in `Operations/PadBack.lean`.
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
/-- The `p` count of `padBack`'s result. -/
theorem PolyZonotope.padBack_p (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).p = pZ.p + r := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
