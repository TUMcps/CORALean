module

public import CORALean.Global.Tensor
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A member of a Minkowski sum of boxed segments is entrywise bounded

`MatExp.abs_entry_le_of_mem_sum`: a member of `⊕ₖ [a_k, 0] B_k` is entrywise within
`Σₖ |a_k| |(B_k)_{ij}|` of `0`. Shared by `abs_entry_le_of_mem_stateCorrectionSet` and
`abs_entry_le_of_mem_inputCorrectionSet`, so it is public rather than `aux_`-named.

## Inputs
* `s` – index set
* `a` – segment ends
* `B` – boxed matrices
* `M` – member matrix
* `i` – row index
* `j` – column index

## Hypotheses
* `hM` – member of the Minkowski sum of boxed segments

## Conclusion
* the entry is bounded by the weighted sum of the matrices' entries
-/

-- Authors:       Claude Sonnet 5
-- Written:       23-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Pointwise

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- A member of `⊕ₖ [a_k, 0] B_k` is entrywise within `Σₖ |a_k| |(B_k)_{ij}|` of `0`. -/
theorem MatExp.abs_entry_le_of_mem_sum (s : Finset ℕ) (a : ℕ → ℝ) (B : ℕ → Mat ℝ n n)
    {M : Mat ℝ n n} (hM : M ∈ ∑ k ∈ s, (fun r : ℝ => r • B k) '' Set.Icc (a k) 0) (i j : Fin n) :
    |M i j| ≤ ∑ k ∈ s, |a k| * |B k i j| := by -- --- PROOF ---
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum s _ M).mp hM
  rw [Matrix.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  obtain ⟨r, ⟨hr1, hr2⟩, hrk⟩ := hg hk
  have hgk : g k i j = r * B k i j := by rw [← hrk]; rfl
  -- a point of `[a_k, 0]` is no larger in magnitude than `a_k`
  have hr : |r| ≤ |a k| := by
    rw [abs_of_nonpos hr2, abs_of_nonpos (hr1.trans hr2)]
    linarith
  rw [hgk, abs_mul]
  exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
