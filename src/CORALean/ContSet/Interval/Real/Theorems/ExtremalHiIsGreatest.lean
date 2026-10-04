import CORALean.ContSet.Interval.Real.Operations.ExtremalHi
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Bounds.Basic

/-!
# `g̅[Y]` is the greatest value of `g[Y]`

The mirror image of `Interval.extremalLo_isLeast`, [1, Remark (optimal)]: at each `x`,
`g̅[Y](x)` is the greatest of `Σᵢ cᵢ hᵢ(x)` over `cᵢ ∈ [cᵢ]`, and is taken. Its upper-bound half
is [1, Sec. 3 (extremal bounds)]'s `f(x, y) ≤ g̅(x)`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.extremalHi_isGreatest (C : Interval (Vec ℝ m)) (hC : C.IsNonempty)
    (h : Vec ℝ m) :
    IsGreatest {s | ∃ c ∈ C.construct, s = ∑ i, c i * h i} (C.extremalHi h) := by -- --- PROOF ---
  constructor
  · -- the corner the signs select is a coefficient vector in `C`
    refine ⟨fun i => if 0 ≤ h i then C.sup i else C.inf i, fun i => ?_, rfl⟩
    have hi : C.inf i ≤ C.sup i := hC i
    change C.inf i ≤ (if 0 ≤ h i then C.sup i else C.inf i) ∧
      (if 0 ≤ h i then C.sup i else C.inf i) ≤ C.sup i
    split_ifs
    · exact ⟨hi, le_rfl⟩
    · exact ⟨le_rfl, hi⟩
  · -- termwise: the selected bound times `hᵢ(x)` is the greatest product
    rintro s ⟨c, hc, rfl⟩
    refine Finset.sum_le_sum fun i _ => ?_
    have hci : C.inf i ≤ c i ∧ c i ≤ C.sup i := hc i
    split_ifs with hh
    · exact mul_le_mul_of_nonneg_right hci.2 hh
    · exact mul_le_mul_of_nonpos_right hci.1 (not_le.mp hh).le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
