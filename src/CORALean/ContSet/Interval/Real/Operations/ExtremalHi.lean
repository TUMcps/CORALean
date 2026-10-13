import CORALean.ContSet.Interval.Real.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# `Interval.extremalHi`

[1, Sec. 3 (extremal bounds)]: for `g[Y](x) = Σᵢ [cᵢ] hᵢ(x)`, the upper extremal function
`g̅[Y](x) = Σᵢ cᵢ⁺(x) hᵢ(x)`, each coefficient read off `[cᵢ]` at the bound the sign of `hᵢ(x)`
selects: the upper one where `hᵢ(x) ≥ 0`, the lower one where `hᵢ(x) ≤ 0`. The coefficient box
is `C` and `h` the vector of values `hᵢ(x)` at one `x`, every index summed, the constant
term included: the paper sums from `i = 1` while its `g[Y]` and its example start at `i = 0`.

## References

* [1] G. Trombettoni, Y. Papegay, G. Chabert and O. Pourtallier. "A Box-Consistency Contractor
      Based on Extremal Functions". In Proc. of the 16th International Conference on Principles
      and Practice of Constraint Programming (CP 2010), LNCS 6308, pp. 491-498, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `g̅[Y](x)` at the values `h = (hᵢ(x))ᵢ` and the coefficient box `C = ([cᵢ])ᵢ`. -/
noncomputable def Interval.extremalHi (C : Interval (Vec ℝ m)) (h : Vec ℝ m) : ℝ :=
  ∑ i, (if 0 ≤ h i then C.sup i else C.inf i) * h i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
