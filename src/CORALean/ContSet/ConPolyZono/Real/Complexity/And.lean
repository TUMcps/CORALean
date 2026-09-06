import CORALean.ContSet.ConPolyZono.Real.Operations.And

/-!
# `ConPolyZono.and`'s counts

`and` runs `andDep` on the two `dependent` sets: every independent generator is
freed into a factor first, so the two operands' `p` and `h` each carry their
own `q` along before the two combine, the independent block empties, `m` picks
up one row per output coordinate, and `s` gains one constraint generator per
freed dependent generator. `rfl` by unfolding `dependent` and `andDep` rather
than restating either.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.and_p (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and C₁ C₂).p = (C₁.p + C₁.q) + (C₂.p + C₂.q) := rfl

theorem ConPolyZono.and_h (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and C₁ C₂).h = (C₁.h + C₁.q) + (C₂.h + C₂.q) := rfl

theorem ConPolyZono.and_q (C₁ C₂ : ConPolyZono (Vec ℝ n)) : (ConPolyZono.and C₁ C₂).q = 0 := rfl

theorem ConPolyZono.and_m (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and C₁ C₂).m = C₁.m + C₂.m + n := rfl

theorem ConPolyZono.and_s (C₁ C₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and C₁ C₂).s = C₁.s + C₂.s + ((C₁.h + C₁.q) + (C₂.h + C₂.q)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
