module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `ConZonotope.reduce`'s constraint counts

Only a bound, and only on the constraints: above the order, the enclosing zonotope is reduced and
reconverted, which drops every constraint down to `fullspace`'s zero; at or below it, `cZ` passes
through unchanged. Either way neither count grows, so `≤ cZ.P.m` and `≤ cZ.P.me` hold
unconditionally: `0 ≤ ·` in the first branch, `rfl` in the second.

The generator count is `ConZonotope.reduce_order_le`, under `Theorems/`: it is `reduce`'s own bound,
not one operation's size in terms of another's, which is what `Complexity/Space/` records.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reducing does not increase the inequality count
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An upper bound on the `P_m` count of `reduce`'s result. -/
theorem ConZonotope.reduce_P_m_le (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    (cZ.reduce o).P.m ≤ cZ.P.m := by
  unfold ConZonotope.reduce
  by_cases h : o * n < cZ.h
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
