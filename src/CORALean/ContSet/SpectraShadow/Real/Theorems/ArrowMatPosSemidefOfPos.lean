import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatQuadForm
import CORALean.ContSet.SpectraShadow.Real.Theorems.ArrowMatIsHermitian
import Mathlib.Analysis.Matrix.Order

/-!
# The arrowhead matrix at `s > 0`

For `s > 0` and `‖w‖² ≤ s t` the arrowhead matrix is positive semidefinite: `s` times its quadratic
form is `‖s y + a w‖² + a² (s t - ‖w‖²)`, a sum of squares and a non-negative multiple of one.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Real

open Matrix

variable {N : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem arrowMat_posSemidef_of_pos {s t : ℝ} {w : Vec ℝ N} (hs : 0 < s)
    (ht : w ⬝ᵥ w ≤ s * t) : (arrowMat s t w).PosSemidef := by -- --- PROOF ---
  refine PosSemidef.of_dotProduct_mulVec_nonneg (arrowMat_isHermitian s t w) fun x => ?_
  rw [star_trivial, arrowMat_quadForm]
  set a := x 0
  set y : Vec ℝ N := fun i => x i.succ
  -- the square `‖s y + a w‖²`
  have h := dotProduct_self_star_nonneg (s • y + a • w)
  simp only [star_trivial, dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul] at h
  rw [dotProduct_comm y w] at h
  -- `s` times the form is that square plus `a² (s t - ‖w‖²)`
  have key : 0 ≤ s * (t * a ^ 2 + 2 * a * (w ⬝ᵥ y) + s * (y ⬝ᵥ y)) := by
    nlinarith [sq_nonneg a, mul_le_mul_of_nonneg_left ht (sq_nonneg a)]
  exact (mul_nonneg_iff_of_pos_left hs).1 key

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
