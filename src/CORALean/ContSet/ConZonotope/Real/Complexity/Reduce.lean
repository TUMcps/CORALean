import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

/-!
# `ConZonotope.reduce`'s constraint counts

Only a bound, and only on the constraints: above the order, the enclosing
zonotope is reduced and reconverted, which drops every constraint down to
`fullspace`'s zero; at or below it, `C` passes through unchanged and both
counts are exactly what they were. Either way neither count grows, so
`≤ C.P.m` and `≤ C.P.me` hold unconditionally: `0 ≤ ·` in the first branch,
`rfl` in the second once it is fixed.

No generator-count bound is stated: that would need `Zonotope.reduce`'s own
order bound, which does not exist — `Zonotope`'s `Complexity/ReduceBy.lean`
bounds `reduceCombastel` only, Girard's identical argument deliberately left
unstated (`Theorems/ReduceOrder.lean` says why), and `reduce` calls Girard's.
Reproving it here to fill this file would be inventing a bound issue #5 asks
this directory not to.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
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
