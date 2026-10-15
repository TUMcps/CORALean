module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Plus
public import CORALean.ContSet.Zonotope.Real.Complexity.Space.Theorems.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Tactic.Positivity
public import CORALean.ContSet.ZonoBundle.Real.Complexity.Space.Theorems.PlusK

@[expose] public section

/-!
# `ZonoBundle.plus_k_isBigO`

The `k` count of `plus`'s result in `O`-notation.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   13-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
/-- The `k` count of `plus`'s result in `O`-notation. -/
theorem ZonoBundle.plus_k_isBigO (zB W : ℕ → ZonoBundle α) (hB : ∀ m, (zB m).k = m)
    (hW : ∀ m, (W m).k = m) :
    (fun m : ℕ => (((ZonoBundle.plus (zB m) (W m)).k : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hk : (ZonoBundle.plus (zB m) (W m)).k = m * m := by
    rw [ZonoBundle.plus_k, hB, hW]
  rw [hk, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg (m : ℝ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
