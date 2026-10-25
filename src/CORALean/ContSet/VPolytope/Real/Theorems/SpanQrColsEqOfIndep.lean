module

public import CORALean.Global.Tensor
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# The basis of the affine hull from a QR decomposition, with pivoting

[1, Eq. 20] takes the first `r = rank V̄` columns of `Q` in `QR = V̄` as a basis of the column
space of `V̄ = [v₁ - v̄ … vₘ - v̄]`, the direction of the affine hull. That holds when the first `r`
columns of `V̄` are linearly independent — what a column-pivoted QR arranges by permuting the
columns, which leaves the column space alone: each of those columns is a combination of the first
`r` columns of `Q`, `R` being upper triangular, and dimensions do the rest. Without pivoting it
fails (`span_qr_cols_counterexample`). `Q` need not even be orthogonal.

## Inputs
* `V` – vertex matrix
* `Q` – orthogonal factor
* `R` – upper triangular factor

## Hypotheses
* `hQR` – `Q R = V`
* `hR` – `R` upper triangular
* `hrk` – `r ≤ k`
* `hrn` – `r ≤ n`
* `hrank` – `V` has rank `r`
* `hind` – the first `r` columns of `V` are independent

## Conclusion
* the first `r` columns of `Q` span the columns of `V`

## References

* [1] M. Wetzlinger, V. Kotsev, A. Kulmburg and M. Althoff. "Implementation of Polyhedral Operations
      in CORA 2024". Proceedings of the 11th Int. Workshop on Applied Verification for Continuous
      and Hybrid Systems, 2024.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n k r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem VPolytope.span_qr_cols_eq_of_indep (V : Mat ℝ n k) (Q : Mat ℝ n n) (R : Mat ℝ n k)
    (hQR : Q * R = V) (hR : ∀ (i : Fin n) (j : Fin k), (j : ℕ) < i → R i j = 0) (hrk : r ≤ k)
    (hrn : r ≤ n)
    (hrank : V.rank = r)
    (hind : LinearIndependent ℝ fun j : Fin r => V.col (Fin.castLE hrk j)) : -- --- CONCL ---
    Submodule.span ℝ (Set.range fun j : Fin r => Q.col (Fin.castLE hrn j)) =
      Submodule.span ℝ (Set.range V.col) := by -- --- PROOF ---
  set W := Submodule.span ℝ (Set.range fun j : Fin r => V.col (Fin.castLE hrk j))
  set U := Submodule.span ℝ (Set.range fun j : Fin r => Q.col (Fin.castLE hrn j))
  -- the `j`-th column of `V` only uses the first `j + 1` columns of `Q`
  have hWU : W ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hcol : V.col (Fin.castLE hrk j) = ∑ i, R i (Fin.castLE hrk j) • Q.col i := by
      rw [← hQR]
      funext a
      simp [Matrix.mul_apply, Matrix.col, Finset.sum_apply, mul_comm]
    show V.col (Fin.castLE hrk j) ∈ U
    rw [hcol]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) ≤ j
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, by omega⟩, ?_⟩)
      congr 1
    · rw [hR i _ (by simp only [Fin.val_castLE]; omega), zero_smul]
      exact Submodule.zero_mem _
  -- dimensions: `W` has `r`, `U` at most `r`, the column space exactly `r`
  have hWC : W ≤ Submodule.span ℝ (Set.range V.col) :=
    Submodule.span_mono (Set.range_subset_iff.mpr fun j => ⟨_, rfl⟩)
  have hW : Module.finrank ℝ W = r := by
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hU : Module.finrank ℝ U ≤ r := le_trans (finrank_range_le_card _) (Fintype.card_fin r).le
  have hC : Module.finrank ℝ (Submodule.span ℝ (Set.range V.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols, hrank]
  rw [← Submodule.eq_of_le_of_finrank_le hWU (by omega),
    Submodule.eq_of_le_of_finrank_le hWC (by omega)]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
