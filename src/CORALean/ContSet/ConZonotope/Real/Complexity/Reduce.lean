import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

/-!
# `ConZonotope.reduce`'s constraint counts

Only a bound, and only on the constraints: above the order, the enclosing
zonotope is reduced and reconverted, which drops every constraint down to
`fullspace`'s zero; at or below it, `C` passes through unchanged and both
counts are exactly what they were. Either way neither count grows, so
`≤ C.P.m` and `≤ C.P.me` hold unconditionally: `0 ≤ ·` in the first branch,
`rfl` in the second once it is fixed.

The generator count is `ConZonotope.reduce_order_le`, under `Theorems/` rather
than here: it is `reduce`'s own bound, not one operation's size in terms of
another's, which is what `Complexity/` records.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_P_m_le (C : ConZonotope (Vec ℝ n)) (o : ℕ) :
    (C.reduce o).P.m ≤ C.P.m := by
  unfold ConZonotope.reduce
  by_cases h : o * n < C.h
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]

theorem ConZonotope.reduce_P_me_le (C : ConZonotope (Vec ℝ n)) (o : ℕ) :
    (C.reduce o).P.me ≤ C.P.me := by
  unfold ConZonotope.reduce
  by_cases h : o * n < C.h
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
