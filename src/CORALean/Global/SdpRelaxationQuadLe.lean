module

public import CORALean.Global.PiLpHolder
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The matrix inequality of the semidefinite relaxations bounds the bilinear form

The weak half of [1, Thm. 17] and [1, Thm. 19]. A pair `(v, w)` with
`[Diag(v), 0; 0, H Diag(w) Hᵀ] ≼ [0, Gᵀ; G, 0]` (Eq. 39, Eq. 42) has, at `(α, -z)`,
`0 ≤ -2 zᵀ G α - Σ vⱼ αⱼ² - Σ wᵢ (Hᵀ z)ᵢ²`; Hölder's inequality then gives
`2 zᵀ G α ≤ ‖v‖_{s₁} ‖(αⱼ²)ⱼ‖_{s₁*} + ‖w‖_{s₂} ‖((Hᵀ z)ᵢ²)ᵢ‖_{s₂*}` for any Hölder pairs.

## Inputs
* `s₁` – exponent of the first diagonal norm
* `s₁'` – its conjugate exponent
* `s₂` – exponent of the second diagonal norm
* `s₂'` – its conjugate exponent
* `G` – coupling matrix
* `H` – generator matrix of the second block
* `v` – first diagonal
* `w` – second diagonal
* `α` – coefficient vector
* `z` – dual vector

## Hypotheses
* `hK` – the matrix inequality holds for the diagonals

## Conclusion
* twice the bilinear form is bounded by Hölder products of the diagonals with the squares

## References

* [1] A. Kulmburg, L. Schäfer and M. Althoff. "Approximability of the Containment Problem for
      Zonotopes and Ellipsotopes". IEEE Transactions on Automatic Control, 2025.
-/

-- Authors:       Claude Opus 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped ENNReal
open Matrix

variable {n m l : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem sdp_relaxation_quad_le (s₁ s₁' s₂ s₂' : ℝ≥0∞) [Fact (1 ≤ s₁')] [Fact (1 ≤ s₂')]
    [s₁'.HolderConjugate s₁] [s₂'.HolderConjugate s₂]
    (G : Matrix (Fin n) (Fin m) ℝ) (H : Matrix (Fin n) (Fin l) ℝ) (v : Fin m → ℝ)
    (w : Fin l → ℝ)
    (hK : (fromBlocks 0 Gᵀ G 0 - fromBlocks (diagonal v) 0 0 (H * diagonal w * Hᵀ)).PosSemidef)
    (α : Fin m → ℝ) (z : Fin n → ℝ) : -- --- CONCL ---
    2 * (z ⬝ᵥ (G *ᵥ α)) ≤ ‖WithLp.toLp s₁ v‖ * ‖WithLp.toLp s₁' (fun j => α j ^ 2)‖ +
      ‖WithLp.toLp s₂ w‖ * ‖WithLp.toLp s₂' (fun i => (z ᵥ* H) i ^ 2)‖ := by -- --- PROOF ---
  haveI : Fact (1 ≤ s₁) := ⟨ENNReal.HolderConjugate.one_le s₁ s₁'⟩
  haveI : Fact (1 ≤ s₂) := ⟨ENNReal.HolderConjugate.one_le s₂ s₂'⟩
  have h := hK.dotProduct_mulVec_nonneg (Sum.elim α (-z))
  simp only [star_trivial, sub_mulVec, dotProduct_sub, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, sumElim_dotProduct_sumElim, zero_mulVec, zero_add, add_zero]
    at h
  -- the four blocks
  have h1 : α ⬝ᵥ (Gᵀ *ᵥ -z) = -(z ⬝ᵥ (G *ᵥ α)) := by
    rw [mulVec_neg, dotProduct_neg, mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
  have h2 : -z ⬝ᵥ (G *ᵥ α) = -(z ⬝ᵥ (G *ᵥ α)) := neg_dotProduct _ _
  have h3 : α ⬝ᵥ (diagonal v *ᵥ α) = ∑ j, v j * α j ^ 2 := by
    simp only [mulVec_diagonal, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : -z ⬝ᵥ ((H * diagonal w * Hᵀ) *ᵥ -z) = ∑ i, w i * (z ᵥ* H) i ^ 2 := by
    rw [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, ← mulVec_mulVec, ← mulVec_mulVec,
      dotProduct_mulVec, mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2, h3, h4] at h
  -- Hölder on both diagonal terms
  have hv := piLp_sum_mul_le_norm_mul_norm s₁' s₁ (-v) (fun j => α j ^ 2)
  have hw := piLp_sum_mul_le_norm_mul_norm s₂' s₂ (-w) (fun i => (z ᵥ* H) i ^ 2)
  rw [WithLp.toLp_neg, norm_neg] at hv hw
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at hv hw
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
