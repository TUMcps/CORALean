import CORALean.ContSet.Zonotope.Real.Zonotope
import CORALean.ContSet.Interval.Real.Operations.Center
import CORALean.ContSet.Interval.Real.Operations.Radius
import Mathlib.Data.Matrix.Mul

/-!
# `Zonotope.inclusion`

The zonotope inclusion of [1, Prop. 4], which is [2, Thm. 4]: the family `p ⊕ [M] Bᵐ`, one zonotope
for every matrix `M` of the interval matrix `[M]`, lies in `p ⊕ [mid[M] rs(rad[M])] Bᵐ⁺ⁿ`, the
centre matrix's columns and then one axis-aligned generator per row, of length that row's radius
sum (`rs`, the row-sum diagonal matrix of [1, Sec. 2]). The enclosure is `inclusion_outer`.

## References

* [1] V. T. H. Le, C. Stoica, T. Alamo, E. F. Camacho and D. Dumur. "Zonotopic guaranteed state
      estimation for uncertain systems". Automatica, 49(11):3418-3424, 2013.
* [2] T. Alamo, J. M. Bravo and E. F. Camacho. "Guaranteed state estimation by zonotopes".
      Automatica, 41(6):1035-1043, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `p ⊕ [mid[M]  rs(rad[M])] Bᵐ⁺ⁿ`. -/
noncomputable def Zonotope.inclusion (p : Vec ℝ n) (IM : Interval (Mat ℝ n m)) :
    Zonotope (Vec ℝ n) :=
  let midM : Fin m → Vec ℝ n := fun j i => IM.center i j               -- columns of mid[M]
  let rsRad : Mat ℝ n n := Matrix.diagonal fun i => ∑ j, IM.radius i j  -- rs(rad[M])
  { h := m + n
    c := p
    G := Fin.append midM fun l => rsRad l }

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
