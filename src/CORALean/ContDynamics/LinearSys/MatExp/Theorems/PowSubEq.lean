import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Tactic.FieldSimp
/-!
# `t^m - (t/r) r^m`, factored through `s = t/r`

Both correction matrices bound this quantity by first replacing it with
`r^m * (s^m - s)`, which is what lets a scalar bound on `[0,1]` — stated in
`s` alone — reach a claim stated in `t` and `r`.
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

/-- Rewriting one order of the interpolation error through `s = t/r`. -/
theorem pow_sub_eq {t r : ℝ} (hr : 0 < r) (m : ℕ) :
    t ^ m - (t / r) * r ^ m = r ^ m * ((t / r) ^ m - (t / r)) := by
  rw [div_pow]
  field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
