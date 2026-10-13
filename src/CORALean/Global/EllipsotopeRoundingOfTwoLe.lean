import CORALean.Global.LpNormLeLpNorm
import CORALean.Global.LpNormLeCardRpowMul
import CORALean.Global.NormTwoTransposeMulVecEq
import CORALean.Global.NormTwoMulVecLe

/-!
# Rounding an ellipsotope by the Euclidean ball, `q ≥ 2`

`[1, App. B]`: for `M` with orthonormal rows (`M Mᵀ = I`, the `D⁻¹Uᵀ H = [I 0] Vᵀ` of its SVD)
and `q ≥ 2`, `B₂ ⊆ E_q(M) ⊆ m^{1/2-1/q} B₂`, `E_q(M) = {M β | ‖β‖_q ≤ 1}`. The exponent is
the dimension `m` of the coefficient space `B_q` lives in, not the printed `n`, which is the
dimension of the image (`ellipsotope_rounding_counterexample`). A point `y` of `B₂` is `M (Mᵀ y)`
with `‖Mᵀ y‖_q ≤ ‖Mᵀ y‖₂ = ‖y‖₂`, and `‖M β‖₂ ≤ ‖β‖₂ ≤ m^{1/2-1/q} ‖β‖_q`.

## References

* [1] A. Kulmburg, I. Brkan and M. Althoff. "Search-based and Stochastic Solutions to the
      Zonotope and Ellipsotope Containment Problems". In Proc. of the European Control
      Conference (ECC), 2024. doi:10.23919/ECC64448.2024.10590884.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open WithLp Matrix ENNReal

variable {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ellipsotope_rounding_of_two_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 2 ≤ q) (M : Mat ℝ n m)
    (hM : M * Mᵀ = 1) :
    {y : Fin n → ℝ | ‖toLp 2 y‖ ≤ 1} ⊆ {y | ∃ β : Fin m → ℝ, ‖toLp q β‖ ≤ 1 ∧ y = M *ᵥ β} ∧
      {y | ∃ β : Fin m → ℝ, ‖toLp q β‖ ≤ 1 ∧ y = M *ᵥ β}
        ⊆ {y | ‖toLp 2 y‖ ≤ (m : ℝ) ^ (2⁻¹ - q⁻¹).toReal} := by -- --- PROOF ---
  refine ⟨fun y hy => ?_, ?_⟩
  · -- `y = M (Mᵀ y)`, and `Mᵀ y` is in the `ℓ_q` ball since the `ℓ_q` norm is below the `ℓ₂` norm
    refine ⟨Mᵀ *ᵥ y, ?_, by rw [mulVec_mulVec, hM, one_mulVec]⟩
    exact (lpNorm_le_lpNorm hq (by simp) (Mᵀ *ᵥ y)).trans
      ((norm_two_transpose_mulVec_eq M hM y).trans_le hy)
  · rintro _ ⟨β, hβ, rfl⟩
    refine (norm_two_mulVec_le M hM β).trans ((lpNorm_le_card_rpow_mul hq (by simp) β).trans ?_)
    exact mul_le_of_le_one_right (by positivity) hβ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
