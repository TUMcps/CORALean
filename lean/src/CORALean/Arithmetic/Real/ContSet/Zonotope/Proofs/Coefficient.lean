import CORALean.Arithmetic.Real.ContSet.Zonotope.API

/-!
# Hitting a target with one symmetric generator

A generator of radius `R` reaches exactly `[-R, R]`, so any `D` with `|D| ≤ R`
is `R * coefficient R D` for a coefficient the unit ball allows. At `R = 0` the
same bound pins `D` to zero, so any coefficient does.

Proof devices, not operations, hence here rather than in `API`. `coefficient` is
noncomputable — deciding `R = 0` over ℝ is — but nothing runs it; it only
witnesses an existential.

Both `reduce` and the floating-point `absorbError` need these: each moves a box
into one diagonal block of generators.
-/

-- Authors:       Tobias Ladner
-- Written:       16-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real.Zonotope.Proofs

variable {n : ℕ}

noncomputable def coefficient (R D : ℝ) : ℝ := if R = 0 then 0 else D / R

theorem abs_coefficient_le_one {R D : ℝ} (hR : 0 ≤ R) (hDR : |D| ≤ R) :
    |coefficient R D| ≤ 1 := by
  rw [coefficient]
  split
  · simp
  · rw [abs_div, abs_of_nonneg hR, div_le_one (lt_of_le_of_ne hR (by tauto))]
    exact hDR

theorem mul_coefficient {R D : ℝ} (hDR : |D| ≤ R) : R * coefficient R D = D := by
  rw [coefficient]
  by_cases h0 : R = 0
  · simp only [h0, if_pos, zero_mul]
    exact (abs_eq_zero.mp (le_antisymm (h0 ▸ hDR) (abs_nonneg _))).symm
  · rw [if_neg h0]; field_simp

/-- A diagonal block couples each coordinate to one coefficient and no other. -/
theorem sum_diagonal_mul (v g : Vec ℝ n) (i : Fin n) :
    ∑ i', Matrix.diagonal v i i' * g i' = v i * g i := by
  rw [Finset.sum_eq_single i, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Matrix.diagonal_apply_ne' _ hb, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end CORALean.Arithmetic.Real.Zonotope.Proofs
