module

public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxExpGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Complexity.Time.Operations.RelaxGreedyCost
public import CORALean.ContSet.PolyZonotope.Real.Operations.RelaxGreedy
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Prod

@[expose] public section

/-!
# `PolyZonotope.relaxGreedyCost_isBigO`

[1, Thm. 2 (complexity)]: `Alg. 2` is `O((h + q) h n + h² p)`.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the cost grows at most like the product bound in the four sizes

## References

* [1] T. Ladner and M. Althoff. "Exponent Relaxation of Polynomial Zonotopes and Its
      Applications in Formal Neural Network Verification". AAAI, 2024.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The count itself, at most eight times the bound, from `p = 1` on. -/
theorem aux_relaxGreedyCost_ops_le (h q n p : ℕ) (hp : 1 ≤ p) :
    (PolyZonotope.relaxGreedyCost h q n p).ops
      ≤ 8 * ((h + q) * h * n + h ^ 2 * p) := by -- --- PROOF ---
  simp only [PolyZonotope.relaxGreedyCost, Cost.ops_add, Cost.ops_smul]
  have h1 : h ^ 2 ≤ h ^ 2 * p := Nat.le_mul_of_pos_right _ hp
  have h2 : h * (h + (n * (1 + 2 * h + q) + h * p)) =
      h ^ 2 + h * n + 2 * (h ^ 2 * n) + h * q * n + h ^ 2 * p := by ring
  have h3 : h * n ≤ h ^ 2 * n := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp
    · exact Nat.mul_le_mul_right n (by nlinarith)
  have h4 : (h + q) * h * n = h ^ 2 * n + h * q * n := by ring
  rw [h2, h4]
  linarith [h1, h3, Nat.zero_le (h ^ 2 * n), Nat.zero_le (h * q * n), Nat.zero_le (h ^ 2),
    Nat.zero_le (h * n), Nat.zero_le (h ^ 2 * p)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Thm. 2 (complexity)]: `Alg. 2` is `O((h + q) h n + h² p)`. -/
theorem PolyZonotope.relaxGreedyCost_isBigO : -- --- CONCL ---
    (fun x : ℕ × ℕ × ℕ × ℕ => ((PolyZonotope.relaxGreedyCost x.1 x.2.1 x.2.2.1 x.2.2.2).ops : ℝ))
      =O[Filter.atTop]
        fun x : ℕ × ℕ × ℕ × ℕ =>
          (((x.1 + x.2.1) * x.1 * x.2.2.1 + x.1 ^ 2 * x.2.2.2 : ℕ) : ℝ) := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 8
  filter_upwards [Filter.eventually_ge_atTop ((0, 0, 0, 1) : ℕ × ℕ × ℕ × ℕ)] with x hx
  have hp : 1 ≤ x.2.2.2 := hx.2.2.2
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact_mod_cast aux_relaxGreedyCost_ops_le x.1 x.2.1 x.2.2.1 x.2.2.2 hp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
