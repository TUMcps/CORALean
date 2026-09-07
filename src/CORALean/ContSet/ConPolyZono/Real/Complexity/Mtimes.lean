import CORALean.ContSet.ConPolyZono.Real.Operations.Mtimes

/-!
# `ConPolyZono.mtimes`'s counts

`mtimes` is `map` at `A *ᵥ ·`: it touches the centre and both generator blocks
only, so all five counts carry over exactly — the constraint system in
particular is untouched, since `M` never reaches `A`, `b` or `EC`. `rfl`
against the structure instance in `Operations/Mtimes.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {k n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.mtimes_p (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).p = cPZ.p := rfl

theorem ConPolyZono.mtimes_h (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).h = cPZ.h := rfl

theorem ConPolyZono.mtimes_q (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).q = cPZ.q := rfl

theorem ConPolyZono.mtimes_m (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).m = cPZ.m := rfl

theorem ConPolyZono.mtimes_s (M : Mat ℝ k n) (cPZ : ConPolyZono (Vec ℝ n)) :
    (ConPolyZono.mtimes M cPZ).s = cPZ.s := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
