module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic

@[expose] public section

/-!
# A matrix acts on the two parts of the plant's input separately

`B [a; e] = B(:, 1:m) a + B(:, m+1:end) e`: CORA's split of `B` into `B_nn` and `B_ext` in
`aux_augmentLinear`, `leftCols` and `rightCols`. Over the rows' sum, cut at `m`.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

theorem mulVec_joinInput {n M m : ℕ} (hm : m ≤ M) (B : Mat ℝ n M) (a : Vec ℝ m)
    (e : Vec ℝ (M - m)) :
    B *ᵥ joinInput hm a e = leftCols hm B *ᵥ a + rightCols hm B *ᵥ e := by -- --- PROOF ---
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hk : m + k - m = k := by omega
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, leftCols, rightCols, Matrix.of_apply]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [joinInput, Fin.val_castAdd, j.isLt, dite_true]
    rfl
  · rw [← Fin.sum_congr' _ hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [joinInput, Fin.val_natAdd, Fin.val_cast]
    simp
    left
    rfl

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
