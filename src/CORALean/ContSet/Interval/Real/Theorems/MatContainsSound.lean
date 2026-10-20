module

public import CORALean.ContSet.Interval.Real.Definitions.MatContains

@[expose] public section

/-!
# `Interval.matContains` holds only within the tolerance of the box

Each of the three tests that admit a bound moves it by at most `tol * max 1 |M i j|`: the strict
test by `tol`, the absolute test by `tol`, the relative one by `tol * |M i j|`. A column that
`matContains` accepts is nonempty.

## Inputs
* `A` – interval matrix
* `M` – real matrix
* `tol` – tolerance
* `i` – row index
* `j` – column index

## Hypotheses
* `ht` – tolerance nonnegative
* `h` – containment up to tolerance holds

## Conclusion
* the entry lies within the tolerance of the bounds
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       14-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A matrix accepted with tolerance `tol ≥ 0` is within `tol * max 1 |M i j|` of its entry's
interval, and every column of the box is nonempty. -/
theorem Interval.matContains_sound (A : Interval (Mat ℝ m n)) (M : Mat ℝ m n) {tol : ℝ}
    (ht : 0 ≤ tol) (h : A.matContains M tol) (i : Fin m) (j : Fin n) :
    A.inf i j ≤ A.sup i j ∧ A.inf i j - tol * max 1 |M i j| ≤ M i j ∧
      M i j ≤ A.sup i j + tol * max 1 |M i j| := by -- --- PROOF ---
  obtain ⟨hne, h2⟩ := h j
  obtain ⟨h3, h4⟩ := h2 i
  have hm1 : tol ≤ tol * max 1 |M i j| := by
    nlinarith [le_max_left 1 |M i j|]
  have hm2 : tol * min |A.inf i j| |M i j| ≤ tol * max 1 |M i j| :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) ht).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
  have hm3 : tol * min |A.sup i j| |M i j| ≤ tol * max 1 |M i j| :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) ht).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)
  refine ⟨hne i, ?_, ?_⟩
  · rcases h3 with h | h | h
    · linarith
    · linarith [(abs_le.mp h).1, (abs_le.mp h).2]
    · linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  · rcases h4 with h | h | h
    · linarith
    · linarith [(abs_le.mp h).1, (abs_le.mp h).2]
    · linarith [(abs_le.mp h).1, (abs_le.mp h).2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
