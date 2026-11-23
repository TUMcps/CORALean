module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A product is a difference of two squares

CORA.cpp lowers a product `a b` of two values to `((a + b) / 2)² - ((a - b) / 2)²`: a dense map to
the half sum and the half difference, the square layer, and the map `(1, -1)`. The identity is
exact, so the exact maps around a sound square enclosure enclose the product.

## Inputs
* `a` – first value
* `b` – second value

## Hypotheses
* none

## Conclusion
* the product is the square of the half sum minus the square of the half difference
-/

-- Authors:       Claude Opus 5.5
-- Written:       23-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem mul_eq_sq_sub_sq (a b : ℝ) :
    a * b = ((a + b) / 2) ^ 2 - ((a - b) / 2) ^ 2 := by
  ring


end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
