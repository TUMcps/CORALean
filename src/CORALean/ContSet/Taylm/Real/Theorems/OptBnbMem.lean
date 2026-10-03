import CORALean.ContSet.Taylm.Real.Operations.OptBnb
import CORALean.ContSet.Taylm.Real.Theorems.BranchAndBoundMem
import Mathlib.Tactic.Linarith

/-!
# `Taylm.optBnb` bounds the enclosed function

On the normalized box the polynomial lies in the branch and bound interval, [1, Alg. 1], and the
function differs from it by the remainder.

## References

* [1] M. Althoff, D. Grebenyuk, and N. Kochdumper. "Implementation of Taylor Models in CORA
      2018". In Proc. of the 5th International Workshop on Applied Verification of Continuous
      and Hybrid Systems (ARCH18), EPiC Series in Computing, vol. 54, pp. 145-173, 2018.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.optBnb_mem {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) (ε : ℝ) (fuel : ℕ)
    {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    (T.optBnb ε fuel).1 ≤ f t ∧ f t ≤ (T.optBnb ε fuel).2 := by -- --- PROOF ---
  have hb := Taylm.branchAndBound_mem T.terms (fun _ => (-1, 1)) ε false fuel (t := t)
    fun k => abs_le.1 (ht k)
  have hr := h t ht
  simp only [Taylm.poly] at hr
  simp only [Taylm.optBnb]
  constructor <;> linarith [hb.1, hb.2, hr.1, hr.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
