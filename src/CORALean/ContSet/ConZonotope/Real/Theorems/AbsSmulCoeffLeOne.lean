module

public import CORALean.ContSet.ConZonotope.Real.ConZonotope

@[expose] public section

/-!
# A weighted coefficient block stays admissible

What a convex combination needs of the coefficients it hands each side: scaling
an admissible block by a weight in `[0,1]` keeps every entry in `[-1,1]`, so the
two sides can be carried at once. Both layers' `linComb` states it of the same
blocks, which is why it is here rather than inside one of them.

## Inputs
* `w` – weight
* `h` – number of generators
* `β` – coefficient vector
* `j` – coefficient index

## Hypotheses
* `hw0` – weight nonnegative
* `hw1` – weight at most one
* `hβ` – all coefficients in the unit box

## Conclusion
* the weighted coefficient stays in the unit box
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.abs_smul_coeff_le_one {w : ℝ} {h : ℕ} {β : Fin h → ℝ} (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (hβ : ∀ j, |β j| ≤ 1) (j : Fin h) : |(w • β) j| ≤ 1 := by
  rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hw0]
  exact le_trans (mul_le_of_le_one_right hw0 (hβ j)) hw1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
