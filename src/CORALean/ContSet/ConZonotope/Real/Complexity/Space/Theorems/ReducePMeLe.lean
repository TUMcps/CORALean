module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce

@[expose] public section

/-!
# `ConZonotope.reduce_P_me_le`

An upper bound on the `P_me` count of `reduce`'s result.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* reducing does not increase the equality count
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   07-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- An upper bound on the `P_me` count of `reduce`'s result. -/
theorem ConZonotope.reduce_P_me_le (cZ : ConZonotope (Vec ℝ n)) (o : ℕ) :
    (cZ.reduce o).P.me ≤ cZ.P.me := by
  unfold ConZonotope.reduce
  by_cases h : o * n < cZ.h
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
