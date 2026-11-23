module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A maximum is a ReLU of the difference

CORA.cpp lowers a max pool to `max(a, b) = b + relu(a - b)`, pairwise over the window, round by
round: a map of the differences, the ReLU, and the second item of each pair added back. Each round
computes the maximum of its pairs exactly, so a network of exact affine maps and a sound ReLU
enclosure encloses the max pool.

## Inputs
* `a` – first value
* `b` – second value

## Hypotheses
* none

## Conclusion
* the larger of two values is the second plus the ReLU of their difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem max_eq_add_relu_sub (a b : ℝ) :
    max a b = b + max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
