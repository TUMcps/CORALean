import CORALean.Global.Mathlib

/-!
# A sum with one term zeroed is the sum without it

What meets `Finset.erase` halfway: the zeroed term contributes nothing.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sum_ite_zero (i : Fin n) (h : Fin n → ℝ) :
    ∑ j, (if j = i then (0 : ℝ) else h j) = ∑ j ∈ Finset.univ.erase i, h j := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => if j = i then (0 : ℝ) else h j)
    (Finset.mem_univ i), if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
