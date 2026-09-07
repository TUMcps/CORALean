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

theorem ConPolyZono.and_p (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and cPZ₁ cPZ₂).p = (cPZ₁.p + cPZ₁.q) + (cPZ₂.p + cPZ₂.q) := rfl

theorem ConPolyZono.and_h (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and cPZ₁ cPZ₂).h = (cPZ₁.h + cPZ₁.q) + (cPZ₂.h + cPZ₂.q) := rfl

theorem ConPolyZono.and_q (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and cPZ₁ cPZ₂).q = 0 := rfl

theorem ConPolyZono.and_m (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and cPZ₁ cPZ₂).m = cPZ₁.m + cPZ₂.m + n := rfl

theorem ConPolyZono.and_s (cPZ₁ cPZ₂ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.and cPZ₁ cPZ₂).s = cPZ₁.s + cPZ₂.s + ((cPZ₁.h + cPZ₁.q) + (cPZ₂.h + cPZ₂.q)) := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
