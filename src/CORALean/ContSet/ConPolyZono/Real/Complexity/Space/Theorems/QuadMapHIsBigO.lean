module

public import CORALean.ContSet.ConPolyZono.Real.Operations.QuadMap
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.ConPolyZono.Real.Complexity.Space.Theorems.Basic

@[expose] public section

/-!
# `ConPolyZono.quadMap_h_isBigO`

The `h` count of `quadMap`'s result in `O`-notation.

## Inputs
* `Q` – family of quadratic forms
* `cPZ` – family of operands

## Hypotheses
* `hC` – generator count of the operand of size m is m

## Conclusion
* the dependent generator count grows at most quadratically
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The `h` count of `quadMap`'s result in `O`-notation. -/
theorem ConPolyZono.quadMap_h_isBigO (Q : Fin k → Mat ℝ n n) (cPZ : ℕ → ConPolyZono (Vec ℝ n))
    (hC : ∀ m, (cPZ m).h + (cPZ m).qI = m) : -- --- CONCL ---
    (fun m : ℕ => (((ConPolyZono.quadMap Q (cPZ m)).h : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 4
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hh : (ConPolyZono.quadMap Q (cPZ m)).h = (m + 1) * (m + 1) := by
    rw [ConPolyZono.quadMap_h, hC]
  have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [hh, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg ((m : ℝ) - 1)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
