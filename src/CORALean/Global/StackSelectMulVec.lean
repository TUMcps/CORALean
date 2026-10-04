import CORALean.Global.StackSelect

/-!
# The selection matrices pick their block

`[eye zeros] [a; b] = a` and `[zeros eye] [a; b] = b`.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n r : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem stackFst_mulVec (a : Vec ℝ n) (b : Vec ℝ r) :
    stackFst n r *ᵥ (Fin.append a b : Vec ℝ (n + r)) = a := by -- --- PROOF ---
  funext i
  -- split the sum over `Fin (n + r)` into its two halves
  simp only [Matrix.mulVec, dotProduct, stackFst, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  simp [Fin.val_inj]
  -- the second half lies above `n`, the diagonal below it
  exact Finset.sum_eq_zero fun x _ => by rw [if_neg (by have := i.isLt; omega)]

theorem stackSnd_mulVec (a : Vec ℝ n) (b : Vec ℝ r) :
    stackSnd n r *ᵥ (Fin.append a b : Vec ℝ (n + r)) = b := by -- --- PROOF ---
  funext i
  simp only [Matrix.mulVec, dotProduct, stackSnd, Matrix.of_apply, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  simp only [ite_mul, one_mul, zero_mul, Nat.add_left_cancel_iff, Fin.val_inj,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- the first half lies below `n`, the diagonal above it
  rw [Finset.sum_eq_zero (fun x _ => by rw [if_neg (by omega)]), zero_add]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
