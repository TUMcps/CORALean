import CORALean.Arithmetic.Real.ContSet.Zonotope.API

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

namespace CORALean.Arithmetic.Real.Zonotope.Proofs

variable {n : ℕ}

theorem interval_outer (Z : Zonotope n) : Z.construct ⊆ Z.interval.construct := by
  rintro x ⟨β, hβ, hx⟩ i
  have key : |x i - Z.c i| ≤ ∑ j, |Z.G i j| := by
    rw [hx i, add_sub_cancel_left]
    calc |∑ j, Z.G i j * β j|
        ≤ ∑ j, |Z.G i j * β j|   := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |Z.G i j| * |β j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |Z.G i j|         := by
          refine Finset.sum_le_sum fun j _ => ?_
          simpa using mul_le_mul_of_nonneg_left (hβ j) (abs_nonneg (Z.G i j))
  rw [abs_le] at key
  exact ⟨by simp only [Zonotope.interval]; linarith [key.1],
         by simp only [Zonotope.interval]; linarith [key.2]⟩

end CORALean.Arithmetic.Real.Zonotope.Proofs
