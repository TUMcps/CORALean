module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `P₂` expanded about a point

[1, Sec. 3 (search for x₀)]'s quadratic part `P₂ = c + g ⬝ x + ½ x ⬝ Hx`, `H` symmetric, is exactly
its first two Taylor terms about any `x`: `P₂(x + v) = P₂(x) + ∇P₂(x) ⬝ v + ½ v ⬝ Hv`, with
`∇P₂(x) = g + Hx`. The search for `x₀` reads both its descent and its optimality off this.

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

/-- [1, Sec. 3 (search for x₀)]: `P₂(x + v) - P₂(x) = ∇P₂(x) ⬝ v + ½ v ⬝ Hv`, `H` symmetric. -/
theorem Taylm.qfb_quad_expand {H : Mat ℝ n n} (hH : H.IsSymm) (c : ℝ) (g x v : Vec ℝ n) :
    c + g ⬝ᵥ (x + v) + (x + v) ⬝ᵥ (H *ᵥ (x + v)) / 2
      = c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2 + (g + H *ᵥ x) ⬝ᵥ v + v ⬝ᵥ (H *ᵥ v) / 2 := by
  have hsym : x ⬝ᵥ (H *ᵥ v) = (H *ᵥ x) ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hH.eq, dotProduct_comm]
  simp only [dotProduct_add, add_dotProduct, mulVec_add, hsym, dotProduct_comm v (H *ᵥ x)]
  ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
