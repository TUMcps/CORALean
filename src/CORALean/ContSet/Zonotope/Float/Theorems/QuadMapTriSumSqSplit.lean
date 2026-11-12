module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The ordered pairs of a square, as the diagonal and the entries below it

Real algebra behind `Zonotope.quadMapTri_pairs_split`: the sum over the ordered pairs `(a, b)` of
`0..N` is the diagonal plus, for each column `j < N` and each row `r = j + 1 + t` below it, both
`(r, j)` and `(j, r)`. By induction on `N`: the new index `N + 1` adds one row and one column.

## Inputs
* `F` – the summand, on the naturals
* `N` – largest index

## Hypotheses
* none

## Conclusion
* the double sum splits into the diagonal and the entries below it
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Finset

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The ordered pairs of `0..N` are the diagonal and, for every column `j < N`, the entries
below it in both orders. -/
theorem Zonotope.quadMapTri_sum_sq_split (F : ℕ → ℕ → ℝ) (N : ℕ) : -- --- CONCL ---
    ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), F a b = ∑ a ∈ range (N + 1), F a a +
      ∑ j ∈ range N, ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t)) := by -- --- PROOF ---
  induction N with
  | zero => simp
  | succ N ih =>
    -- the pairs with the new index `N + 1`: one more row in each column, and the new column
    have hnew : ∑ j ∈ range (N + 1), ∑ t ∈ range (N + 1 - j), (F (j + 1 + t) j + F j (j + 1 + t))
        = ∑ j ∈ range N, ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t))
          + ∑ j ∈ range (N + 1), (F (N + 1) j + F j (N + 1)) := by
      rw [sum_range_succ _ N, sum_range_succ (fun j => (F (N + 1) j + F j (N + 1))) N]
      -- column by column, the new row is the last place of the column
      have h1 : ∀ j ∈ range N, ∑ t ∈ range (N + 1 - j), (F (j + 1 + t) j + F j (j + 1 + t))
          = ∑ t ∈ range (N - j), (F (j + 1 + t) j + F j (j + 1 + t))
            + (F (N + 1) j + F j (N + 1)) := by
        intro j hj
        have hj' := mem_range.mp hj
        rw [show N + 1 - j = (N - j) + 1 by omega, sum_range_succ]
        congr 3 <;> omega
      rw [sum_congr rfl h1, sum_add_distrib]
      simp
      ring
    -- the new row and column of the double sum, against the new pairs
    have hr : ∑ b ∈ range (N + 1), F (N + 1) b + ∑ a ∈ range (N + 1), F a (N + 1)
        = ∑ j ∈ range (N + 1), (F (N + 1) j + F j (N + 1)) := by
      rw [sum_add_distrib]
    rw [hnew, sum_range_succ (fun a => ∑ b ∈ range (N + 1 + 1), F a b) (N + 1)]
    simp only [sum_range_succ (fun b => F _ b) (N + 1), sum_add_distrib] at ih hr ⊢
    linarith [ih, hr]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
