module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The correction's critical point

`corrCritical`: where [1, Thm. 3]'s `s ↦ s ^ i - s` bottoms out: `i ^ (-1/(i-1))`, the only
stationary point, and the minimum because the map is convex.

## Inputs
* `i` – order

## Output
* critical point of the correction polynomial

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control, 2007.
-/

-- Authors:       Claude Sonnet 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Where `s ↦ s ^ i - s` bottoms out: `i ^ (-1/(i-1))`, the only stationary
point, and the minimum because the map is convex. -/
noncomputable def MatExp.corrCritical (i : ℕ) : ℝ :=
  (i : ℝ) ^ (-(1:ℝ) / ((i : ℝ) - 1))

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
