import CORALean.ContSet.Zonotope.Real.Operations.Interval

/-!
# `Zonotope.interval` over-approximates the zonotope

Triangle inequality: coefficients bounded by one make the displacement from the
centre at most the row sum of `|G|`, which is the half-width the hull was given.
`abs_le` turns that into the `inf`/`sup` pair `Interval.construct` asks for.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem Zonotope.interval_outer (Z : Zonotope (Vec ℝ n)) :
    Z.construct ⊆ Z.interval.construct := by
  intro x hxmem
  obtain ⟨β, hβ, hx⟩ := Zonotope.mem_construct_iff.mp hxmem
  intro i
  have key : |x i - Z.c i| ≤ ∑ j, |Z.G j i| := by
    rw [hx i, add_sub_cancel_left]
    calc |∑ j, Z.G j i * β j|
        ≤ ∑ j, |Z.G j i * β j|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |Z.G j i| * |β j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |Z.G j i|         := by
          refine Finset.sum_le_sum fun j _ => ?_
          simpa using mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg (Z.G j i))
  rw [abs_le] at key
  constructor
  · show Z.c i - ∑ j, |Z.G j i| ≤ x i
    linarith [key.1]
  · show x i ≤ Z.c i + ∑ j, |Z.G j i|
    linarith [key.2]

end CORALean.Real
