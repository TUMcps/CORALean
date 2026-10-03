import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The quadratic fast bounder at the quadratic part's minimizer

[1, Sec. 3]: if `x₀` minimizes the quadratic part `P₂ = c + g ⬝ x + ½ x ⬝ H x` (`H` symmetric)
over a convex `D`, it also minimizes the remainder `P₂ - Q_{x₀}`, which is affine with slope
`∇P₂(x₀)`: the first-order condition at a minimizer, here from the quadratic along each segment.

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

theorem Taylm.qfb_optimal {H : Mat ℝ n n} (hH : H.IsSymm) (c : ℝ) (g : Vec ℝ n)
    {D : Set (Vec ℝ n)} (hD : Convex ℝ D) {x0 : Vec ℝ n} (hx0 : x0 ∈ D)
    (hmin : IsMinOn (fun x => c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2) D x0) :
    IsMinOn (fun x => c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2 - (x - x0) ⬝ᵥ (H *ᵥ (x - x0)) / 2)
      D x0 := by -- --- PROOF ---
  -- `x ⬝ H y = y ⬝ H x`
  have hsym : ∀ x y : Vec ℝ n, x ⬝ᵥ (H *ᵥ y) = y ⬝ᵥ (H *ᵥ x) := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hH.eq, dotProduct_comm]
  have hcomm : ∀ x y : Vec ℝ n, (H *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (H *ᵥ y) := by
    intro x y
    rw [dotProduct_comm, hsym]
  intro x hx
  simp only [Set.mem_setOf_eq]
  set v := x - x0
  -- the directional derivative of the quadratic at its minimizer is nonnegative
  have hd : 0 ≤ (g + H *ᵥ x0) ⬝ᵥ v := by
    by_contra hneg
    push Not at hneg
    set a := -((g + H *ᵥ x0) ⬝ᵥ v)
    set b := v ⬝ᵥ (H *ᵥ v)
    have ha : 0 < a := by simp only [a]; linarith
    -- along the segment, `P₂(x₀ + s v) - P₂(x₀) = -a s + b s²/2`
    have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ -a * s + b * s ^ 2 / 2 := by
      intro s hs
      have hmem : x0 + s • v ∈ D := by
        have := hD.add_smul_sub_mem hx0 hx hs
        simpa [v] using this
      have := hmin hmem
      simp only [Set.mem_setOf_eq] at this
      have e : c + g ⬝ᵥ (x0 + s • v) + (x0 + s • v) ⬝ᵥ (H *ᵥ (x0 + s • v)) / 2
          - (c + g ⬝ᵥ x0 + x0 ⬝ᵥ (H *ᵥ x0) / 2) = -a * s + b * s ^ 2 / 2 := by
        simp only [a, b, dotProduct_add, add_dotProduct, mulVec_add, mulVec_smul,
          dotProduct_smul, smul_dotProduct, smul_eq_mul, hsym v x0, hcomm]
        ring
      linarith
    -- a small step along the segment would go below the minimum
    rcases le_or_gt b 0 with hb | hb
    · have := hseg 1 ⟨zero_le_one, le_refl _⟩
      nlinarith
    · set s := min 1 (a / b)
      have hs0 : 0 < s := lt_min one_pos (div_pos ha hb)
      have hs1 : s ≤ 1 := min_le_left _ _
      have hsab : s * b ≤ a := by
        have := min_le_right 1 (a / b)
        rwa [le_div_iff₀ hb] at this
      have := hseg s ⟨hs0.le, hs1⟩
      nlinarith
  -- the difference from the minimizer is that derivative
  have e : c + g ⬝ᵥ x + x ⬝ᵥ (H *ᵥ x) / 2 - (x - x0) ⬝ᵥ (H *ᵥ (x - x0)) / 2
      - (c + g ⬝ᵥ x0 + x0 ⬝ᵥ (H *ᵥ x0) / 2 - (x0 - x0) ⬝ᵥ (H *ᵥ (x0 - x0)) / 2)
      = (g + H *ᵥ x0) ⬝ᵥ v := by
    simp only [v, sub_self, zero_dotProduct, dotProduct_sub, sub_dotProduct, mulVec_sub,
      add_dotProduct, hsym x0 x, hcomm]
    ring
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
