import CORALean.ContSet.Interval.Real.Operations.ExtremalLo
import CORALean.ContSet.Interval.Real.Operations.IsNonempty
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Bounds.Basic

/-!
# `g̲[Y]` is the least value of `g[Y]`

[1, Remark (optimal)]: `g̲[Y]` and `g̅[Y]` are optimal extremal functions of `g[Y]`. At each `x`,
`g̲[Y](x)` is the least of `Σᵢ cᵢ hᵢ(x)` over the coefficients `cᵢ ∈ [cᵢ]`: no smaller value is
taken, and `g̲[Y](x)` is taken, at the corner the signs of `hᵢ(x)` select. That it bounds
`f(x, y)` from below whenever `[cᵢ]` encloses `fᵢ(y)` is the lower-bound half,
[1, Sec. 3 (extremal bounds)].

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

theorem Interval.extremalLo_isLeast (C : Interval (Vec ℝ m)) (hC : C.IsNonempty) (h : Vec ℝ m) :
    IsLeast {s | ∃ c ∈ C.construct, s = ∑ i, c i * h i} (C.extremalLo h) := by -- --- PROOF ---
  constructor
  · -- the corner the signs select is a coefficient vector in `C`
    refine ⟨fun i => if 0 ≤ h i then C.inf i else C.sup i, fun i => ?_, rfl⟩
    have hi : C.inf i ≤ C.sup i := hC i
    change C.inf i ≤ (if 0 ≤ h i then C.inf i else C.sup i) ∧
      (if 0 ≤ h i then C.inf i else C.sup i) ≤ C.sup i
    split_ifs
    · exact ⟨le_rfl, hi⟩
    · exact ⟨hi, le_rfl⟩
  · -- termwise: the selected bound times `hᵢ(x)` is the least product
    rintro s ⟨c, hc, rfl⟩
    refine Finset.sum_le_sum fun i _ => ?_
    have hci : C.inf i ≤ c i ∧ c i ≤ C.sup i := hc i
    split_ifs with hh
    · exact mul_le_mul_of_nonneg_right hci.1 hh
    · exact mul_le_mul_of_nonpos_right hci.2 (not_le.mp hh).le

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
