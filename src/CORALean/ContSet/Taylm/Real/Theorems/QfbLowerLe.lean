import CORALean.ContSet.Taylm.Real.Operations.QfbLower
import CORALean.ContSet.Taylm.Real.Theorems.PolyOfQuadTerms
import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The quadratic fast bounder is a lower bound

[1, Sec. 3]: for a positive semidefinite `H` and any `x₀`, `Q_{x₀} ≥ 0`, so a lower bound of
`f - Q_{x₀}`, which `T - Q_{x₀}` encloses, is one of `f`.

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.qfbLower_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {H : Mat ℝ n n}
    (hH : H.PosSemidef) (x0 : Vec ℝ n) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) :
    T.qfbLower H x0 ≤ f t := by -- --- PROOF ---
  have hQ : (Taylm.quadForm H x0 T.maxOrder).Encloses
      fun t => (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    intro t _
    simp [Taylm.quadForm, Taylm.poly, Taylm.polyOf_quadTerms]
  have hb := Taylm.bounds_mem (Taylm.minus_outer h hQ) ht
  have hq : 0 ≤ (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hH (t - x0)
    simp only [star_trivial] at this
    positivity
  simp only [Taylm.qfbLower]
  linarith [hb.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
