module

public import CORALean.NN.Layers.Definitions.Softmax

@[expose] public section

/-!
# Softmax, divided through by its own term

Dividing through by `exp (x i)`: the `j = i` term becomes exactly `1`, which is what makes the
raw bounds tighter than bounding numerator and denominator apart.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem softmax_eq_inv (x : Vec ℝ n) (i : Fin n) :
    softmax x i = (1 + ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i))⁻¹ := by -- --- PROOF ---
  have hE0 : Real.exp (x i) ≠ 0 := ne_of_gt (Real.exp_pos (x i))
  have hsplit : ∑ j, Real.exp (x j)
      = Real.exp (x i) + ∑ j ∈ Finset.univ.erase i, Real.exp (x j) :=
    (Finset.add_sum_erase Finset.univ (fun j => Real.exp (x j)) (Finset.mem_univ i)).symm
  have hratio : ∑ j ∈ Finset.univ.erase i, Real.exp (x j - x i)
      = (∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => Real.exp_sub (x j) (x i)
  have hone : 1 + (∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i)
      = (Real.exp (x i) + ∑ j ∈ Finset.univ.erase i, Real.exp (x j)) / Real.exp (x i) := by
    field_simp
  show Real.exp (x i) / (∑ j, Real.exp (x j)) = _
  rw [hsplit, hratio, hone, inv_div]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
