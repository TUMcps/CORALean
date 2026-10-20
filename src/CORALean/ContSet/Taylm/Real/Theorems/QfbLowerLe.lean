module

public import CORALean.ContSet.Taylm.Real.Operations.QfbLower
public import CORALean.ContSet.Taylm.Real.Theorems.BoundsMem
public import CORALean.ContSet.Taylm.Real.Theorems.MinusOuter
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfCons
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfNil
public import CORALean.ContSet.Taylm.Real.Theorems.PolyOfQuadTerms
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The quadratic fast bounder is a lower bound

[1, Sec. 3]: for a positive semidefinite `H` and any `x₀`, `Q_{x₀} ≥ 0`, so a lower bound of
`f - Q_{x₀}`, which `T - Q_{x₀}` encloses, is one of `f`.

## Inputs
* `T` – Taylor model
* `f` – enclosed function
* `H` – Hessian matrix
* `x0` – expansion point
* `t` – point

## Hypotheses
* `h` – the model encloses the function
* `hH` – the Hessian is positive semidefinite
* `ht` – point lies in the unit box

## Conclusion
* the quadratic fast bound is at most the function's value

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Taylm.qfbLower_le {T : Taylm n} {f : Vec ℝ n → ℝ} (h : T.Encloses f) {H : Mat ℝ n n}
    (hH : H.PosSemidef) (x0 : Vec ℝ n) {t : Vec ℝ n} (ht : t ∈ Taylm.box n) : -- --- CONCL ---
    T.qfbLower H x0 ≤ f t := by -- --- PROOF ---
  have hQ : (Taylm.aux_quadForm H x0 T.maxOrder).Encloses
      fun t => (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    intro t _
    simp [Taylm.aux_quadForm, Taylm.poly, Taylm.polyOf_quadTerms]
  have hb := Taylm.bounds_mem (Taylm.minus_outer h hQ) ht
  have hq : 0 ≤ (t - x0) ⬝ᵥ (H *ᵥ (t - x0)) / 2 := by
    have := Matrix.PosSemidef.dotProduct_mulVec_nonneg hH (t - x0)
    simp only [star_trivial] at this
    positivity
  simp only [Taylm.qfbLower]
  linarith [hb.1]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
