import CORALean.Global.Tensor
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Order.Filter.Extr

/-!
# The linear system (A.7) solves the estimate's quadratic program

[1, Sec. 4.2 (choice of j)]: the Hausdorff error of eliminating `ξ_j` is estimated by
`H*_j ≡ min{‖Gd‖₂² + ‖d‖₂² : Ad = 0, d_j = r_j}`, and "since this is an equality constrained
quadratic program, its solution `d̂` and duality multipliers `λ̂` are known explicitly as the
solutions of the linear system" (A.7), block by block
`(GᵀG + I)d̂ + Aᵀλ̂ + μ̂e_j = 0`, `Ad̂ = 0`, `e_jᵀd̂ = r_j`. Any solution of the system is a
minimizer. A feasible `d` is `d̂ + e` with `Ae = 0`, `e_j = 0`, the cross term `2eᵀ(GᵀG + I)d̂`
is `-2(Ae)ᵀλ̂ - 2μ̂e_j = 0`, and what is left is `‖Ge‖₂² + ‖e‖₂² ≥ 0`.

## References

* [1] J. K. Scott, D. M. Raimondo, G. R. Marseglia and R. D. Braatz. "Constrained zonotopes:
      A new tool for set-based estimation and fault detection". Automatica, 69:126-136,
      2016.
-/

-- Authors:       Tobias Ladner
-- Written:       10-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Sec. 4.2 (choice of j)]: a solution `(d̂, λ̂, μ̂)` of the linear system minimizes
`‖Gd‖₂² + ‖d‖₂²` over `Ad = 0`, `d_j = r_j`. -/
theorem ConZonotope.hausdorffEstimate_isMinOn {n q h : ℕ} (G : Mat ℝ n h) (A : Mat ℝ q h)
    (j : Fin h) (rj : ℝ) (dHat : Vec ℝ h) (lamHat : Vec ℝ q) (muHat : ℝ)
    (h1 : (Gᵀ * G + 1) *ᵥ dHat + Aᵀ *ᵥ lamHat + muHat • Pi.single j 1 = 0)
    (h2 : A *ᵥ dHat = 0) (h3 : dHat j = rj) :
    IsMinOn (fun d : Vec ℝ h => (G *ᵥ d) ⬝ᵥ (G *ᵥ d) + d ⬝ᵥ d)
      {d | A *ᵥ d = 0 ∧ d j = rj} dHat := by -- --- PROOF ---
  intro d ⟨hAd, hdj⟩
  simp only [Set.mem_setOf_eq]
  set e := d - dHat with he
  have hd : d = dHat + e := by rw [he, add_sub_cancel]
  have hAe : A *ᵥ e = 0 := by rw [he, Matrix.mulVec_sub, hAd, h2, sub_self]
  have hej : e j = 0 := by rw [he, Pi.sub_apply, hdj, h3, sub_self]
  -- the cross term `eᵀ(GᵀG + I)dHat` vanishes on the constraints
  have hcross : (G *ᵥ e) ⬝ᵥ (G *ᵥ dHat) + e ⬝ᵥ dHat = 0 := by
    have hk : e ⬝ᵥ ((Gᵀ * G + 1) *ᵥ dHat + Aᵀ *ᵥ lamHat + muHat • Pi.single j 1) = 0 := by
      rw [h1, dotProduct_zero]
    rw [dotProduct_add, dotProduct_add, dotProduct_smul] at hk
    have hA : e ⬝ᵥ (Aᵀ *ᵥ lamHat) = 0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hAe, zero_dotProduct]
    have hs : e ⬝ᵥ (Pi.single j 1 : Vec ℝ h) = 0 := by
      rw [dotProduct_single, hej, zero_mul]
    have hG : e ⬝ᵥ ((Gᵀ * G + 1) *ᵥ dHat) = (G *ᵥ e) ⬝ᵥ (G *ᵥ dHat) + e ⬝ᵥ dHat := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hA, hs, smul_zero, add_zero, add_zero, hG] at hk
    exact hk
  -- what is left is `‖Ge‖₂² + ‖e‖₂² ≥ 0`
  have hsq : 0 ≤ (G *ᵥ e) ⬝ᵥ (G *ᵥ e) + e ⬝ᵥ e :=
    add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  rw [hd]
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  have c1 := dotProduct_comm (G *ᵥ dHat) (G *ᵥ e)
  have c2 := dotProduct_comm dHat e
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
