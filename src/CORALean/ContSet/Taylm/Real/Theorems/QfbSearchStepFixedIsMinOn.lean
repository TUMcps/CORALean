module

public import CORALean.ContSet.Taylm.Real.Theorems.QfbSearchStepVariational
public import CORALean.ContSet.Taylm.Real.Theorems.QfbQuadExpand
public import Mathlib.Order.Filter.Extr
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# A point the search does not move is the minimizer of `P₂`

[1, Sec. 3 (search for x₀)]: the search for `x₀` is to find "the minimizer of the quadratic part
`P₂` of `P` in `D`". Where the step leaves `x` in place, `x` is that minimizer, for `H` positive
semidefinite and any step length `α > 0`. The projection property at `x⁺ = x` reads
`∇P₂(x) ⬝ (z - x) ≥ 0` for every `z` in the box, and
`P₂(z) - P₂(x) = ∇P₂(x) ⬝ (z - x) + ½ (z - x) ⬝ H(z - x) ≥ 0`.

## Inputs
* `H` – Hessian matrix
* `c` – constant
* `g` – gradient
* `α` – step length
* `x` – point

## Hypotheses
* `hH` – the Hessian is symmetric
* `hP` – the Hessian is positive semidefinite
* `hα` – step length is positive
* `hx` – the search step fixes the point

## Conclusion
* the point minimizes the quadratic part over the unit box

## References

* [1] K. Makino and M. Berz. "Verified Global Optimization with Taylor Model-based Range
      Bounders". Transactions on Computers, 11(4):1611-1618, 2005.
-/

-- Authors:       Claude Opus 5.5
-- Written:       10-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 3 (search for x₀)]: a fixed point of the search step minimizes `P₂` over the box. -/
theorem Taylm.qfbSearchStep_fixed_isMinOn {H : Mat ℝ n n} (hH : H.IsSymm) (hP : H.PosSemidef)
    (c : ℝ) (g : Vec ℝ n) {α : ℝ} (hα : 0 < α) {x : Vec ℝ n}
    (hx : Taylm.qfbSearchStep H g α x = x) : -- --- CONCL ---
    IsMinOn (fun x => c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2) (Taylm.box n) x := by -- --- PROOF ---
  intro z hz
  simp only [Set.mem_setOf_eq]
  -- the projection property at `x⁺ = x`: `∇P₂(x) ⬝ (z - x) ≥ 0`
  have hv := (Taylm.qfbSearchStep_variational H g α x).2 z hz
  rw [hx, sub_sub_cancel_left, neg_dotProduct, smul_dotProduct, smul_eq_mul] at hv
  have hgrad : 0 ≤ (g + H *ᵥ x) ⬝ᵥ (z - x) := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hpsd : 0 ≤ (z - x) ⬝ᵥ (H *ᵥ (z - x)) := by
    simpa using hP.dotProduct_mulVec_nonneg (z - x)
  have := Taylm.qfb_quad_expand hH c g x (z - x)
  rw [add_sub_cancel] at this
  rw [this]
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
