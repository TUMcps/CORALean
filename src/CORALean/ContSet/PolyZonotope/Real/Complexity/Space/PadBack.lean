import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack

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
theorem PolyZonotope.padBack_p (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).p = pZ.p + r := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padBack_h (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).h = pZ.h := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padBack_q (r : ℕ) (pZ : PolyZonotope α) :
    (PolyZonotope.padBack r pZ).q = pZ.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
