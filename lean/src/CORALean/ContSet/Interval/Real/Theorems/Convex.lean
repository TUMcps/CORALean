import CORALean.ContSet.Interval.Real.Interval

/-!
# An interval is convex

Each coordinate is bounded independently, so a weighted average of two admissible
points is admissible coordinate by coordinate. Holds for any bounds, the empty
case included.

What an integral valued in the set needs: an integral is a limit of convex
combinations, so it lands in the set only if the set is convex.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem Interval.convex_construct (I : Interval n) : Convex ℝ I.construct := by
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  -- the weights sum to one, so a constant is its own weighted average
  have hinf : a * I.inf i + b * I.inf i = I.inf i := by rw [← add_mul, hab, one_mul]
  have hsup : a * I.sup i + b * I.sup i = I.sup i := by rw [← add_mul, hab, one_mul]
  constructor
  · show I.inf i ≤ a * x i + b * y i
    linarith [mul_le_mul_of_nonneg_left h1.1 ha, mul_le_mul_of_nonneg_left h2.1 hb]
  · show a * x i + b * y i ≤ I.sup i
    linarith [mul_le_mul_of_nonneg_left h1.2 ha, mul_le_mul_of_nonneg_left h2.2 hb]

end CORALean.Real
