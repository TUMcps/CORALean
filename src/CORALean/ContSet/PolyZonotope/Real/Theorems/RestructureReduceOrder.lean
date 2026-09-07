import CORALean.ContSet.PolyZonotope.Real.Operations.RestructureReduce
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceOrder

/-!
# `restructureReduce` bounds the generator count

What the order argument buys, and what plain `restructure` cannot offer: it adds
`n` generators to whatever it is given, so only a bound on the input bounds the
output. `reduce o` supplies that bound, and the `n` diagonal ones the boxing
frees are all that is added to it.

Stated at `h + q` as `reduce_order_le` is, though `q` is zero here — that is the
count the order of a set means, and reading it back at `h` alone would hide the
`restructure_q` half of the specification.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- At most `o·n` generators survive the reduction, and the boxing adds `n`. -/
theorem PolyZonotope.restructureReduce_order_le (pZ : PolyZonotope (Vec ℝ n)) {o : ℕ}
    (ho : 0 < o) :
    (pZ.restructureReduce o).h + (pZ.restructureReduce o).q
      ≤ (o + 1) * n := by -- --- PROOF ---
  have hred : (pZ.reduce o).h ≤ o * n :=
    (Nat.le_add_right _ _).trans (PolyZonotope.reduce_order_le pZ ho)
  show (pZ.reduce o).h + (0 + n) + 0 ≤ (o + 1) * n
  -- the boxed block is `n` generators on top of whatever the reduction kept
  rw [show (pZ.reduce o).h + (0 + n) + 0 = (pZ.reduce o).h + n by omega, add_mul, one_mul]
  exact Nat.add_le_add_right hred n

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
