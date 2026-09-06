import CORALean.ContSet.PolyZonotope.Real.Operations.PadBack

/-!
# `PolyZonotope.padBack`'s counts

`r` fresh factors after the set's own; the dependent and independent generator
counts stand, since only the factor count and the exponent matrix move. `rfl`
against the structure instance in `Operations/PadBack.lean`.
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
theorem PolyZonotope.padBack_p (r : ℕ) (S : PolyZonotope α) :
    (PolyZonotope.padBack r S).p = S.p + r := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padBack_h (r : ℕ) (S : PolyZonotope α) :
    (PolyZonotope.padBack r S).h = S.h := rfl

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.padBack_q (r : ℕ) (S : PolyZonotope α) :
    (PolyZonotope.padBack r S).q = S.q := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
