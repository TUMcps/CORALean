import CORALean.ContSet.ZonoBundle.Real.Complexity.Plus
import CORALean.Global.Mathlib

/-!
# `ZonoBundle.plus`'s bundle size is `O(m ^ 2)`

Not a bare arithmetic fact about `m * m`, but one tied to `plus` through a
family of bundles whose sizes grow as `m`. `plus_k` reduces the left side to
that product outright, which `m ^ 2` dominates for every `m`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem ZonoBundle.plus_k_isBigO (B W : ℕ → ZonoBundle α) (hB : ∀ m, (B m).k = m)
    (hW : ∀ m, (W m).k = m) :
    (fun m : ℕ => (((ZonoBundle.plus (B m) (W m)).k : ℕ) : ℝ))
      =O[Filter.atTop] fun m : ℕ => ((m : ℝ)) ^ 2 := by -- --- PROOF ---
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  have hk : (ZonoBundle.plus (B m) (W m)).k = m * m := by
    rw [ZonoBundle.plus_k, hB, hW]
  rw [hk, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  push_cast
  nlinarith [sq_nonneg (m : ℝ)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
