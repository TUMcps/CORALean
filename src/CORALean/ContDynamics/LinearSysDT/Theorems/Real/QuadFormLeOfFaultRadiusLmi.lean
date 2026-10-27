module

public import CORALean.ContDynamics.LinearSysDT.Definitions.IsFaultRadiusLmi
public import CORALean.Global.PosDefSchurComplement
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-!
# The fault-observer LMI bounds the P-norm of a step

[1, Eq. 16], [1, Eq. 17]: if `P ≻ 0` and `W` satisfy Eq. 17 (`LinearSysDT.IsFaultRadiusLmi`), then
at the gain `L = P⁻¹W` every `θ`, `s₁`, `s₂` satisfy
`‖(A - LC)θ + D_xH_w s₁ - L D_yH_v s₂‖²_P ≤ γ‖θ‖²_P + ‖D_xH_w s₁‖²₂ + ‖D_yH_v s₂‖²₂`, the inequality
between [1, Eq. 15] and [1, Eq. 16] with `θ` free. That is the paper's derivation run backwards:
the Schur complement of the block `-P` (`posDef_schur_of_fromBlocks`) is
`diag(γP, H_wᵀD_xᵀD_xH_w, H_vᵀD_yᵀD_yH_v) - Ψ`, `Ψ = [A - LC  D_xH_w  LD_yH_v]ᵀ P [⋯]`, whose form
at `(θ, s₁, -s₂)` is the inequality; the sign of the last block of `Ψ` against `-LD_yH_v` in
[1, Eq. 10] is absorbed by the symmetric box. `W = PL` turns Eq. 16 into Eq. 17.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `Dx` – disturbance matrix
* `Hw` – disturbance generators
* `Dy` – noise matrix
* `Hv` – noise generators
* `P` – Lyapunov matrix
* `W` – gain variable
* `γ` – radius bound
* `θ` – error vector
* `s₁` – disturbance coefficients
* `s₂` – noise coefficients

## Hypotheses
* `hP` – Lyapunov matrix positive definite
* `h` – the design inequality holds

## Conclusion
* the P-norm of the error step is bounded

## References

* [1] [Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer with
      H₋ Performance". 2017 36th Chinese Control Conference (CCC),
      2017.](../../../../../../references/2017/wang-ccc-fault-detection-observer.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv rw rv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.quadForm_le_of_isFaultRadiusLmi (A : Mat ℝ n n) (C : Mat ℝ ny n)
    (Dx : Mat ℝ n nw) (Hw : Mat ℝ nw rw) (Dy : Mat ℝ ny nv) (Hv : Mat ℝ nv rv) (P : Mat ℝ n n)
    (W : Mat ℝ n ny) (γ : ℝ) (hP : P.PosDef) (h : LinearSysDT.IsFaultRadiusLmi A C Dx Hw Dy Hv P W
        γ)
    (θ : Vec ℝ n) (s₁ : Vec ℝ rw) (s₂ : Vec ℝ rv) : -- --- CONCL ---
    let L := P⁻¹ * W
    let e := (A - L * C) *ᵥ θ + (Dx * Hw) *ᵥ s₁ - (L * (Dy * Hv)) *ᵥ s₂
    e ⬝ᵥ (P *ᵥ e) ≤ γ * (θ ⬝ᵥ (P *ᵥ θ)) + ((Dx * Hw) *ᵥ s₁) ⬝ᵥ ((Dx * Hw) *ᵥ s₁) +
      ((Dy * Hv) *ᵥ s₂) ⬝ᵥ ((Dy * Hv) *ᵥ s₂) := by -- --- PROOF ---
  intro L e
  haveI : Invertible P := hP.isUnit.invertible
  set Gw := Dx * Hw with hGw
  set Gv := Dy * Hv with hGv
  set TL : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n ⊕ (Fin rw ⊕ Fin rv)) ℝ :=
    fromBlocks (-(γ • P)) 0 0 (fromBlocks (-(Gwᵀ * Gw)) 0 0 (-(Gvᵀ * Gv))) with hTL
  set R : Matrix (Fin n ⊕ (Fin rw ⊕ Fin rv)) (Fin n) ℝ :=
    fromRows (Aᵀ * P - Cᵀ * Wᵀ) (fromRows (Gwᵀ * P) (Gvᵀ * Wᵀ)) with hR
  -- the Schur complement of `-P`
  have hneg : -(fromBlocks TL R Rᵀ (-P)) = fromBlocks (-TL) (-R) (-R)ᵀ P := by
    rw [fromBlocks_neg, transpose_neg, neg_neg]
  have hS := posDef_schur_of_fromBlocks (-TL) (-R) hP (hneg ▸ h)
  have hPT : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  -- `Rᵀ (θ, s₁, -s₂) = P e`, the gain `L = P⁻¹ W` undone
  set v : (Fin n ⊕ (Fin rw ⊕ Fin rv)) → ℝ := Sum.elim θ (Sum.elim s₁ (-s₂))
  have hPL : P * L = W := by
    simp only [L, ← Matrix.mul_assoc, mul_inv_of_invertible, Matrix.one_mul]
  have hRv : Rᵀ *ᵥ v = P *ᵥ e := by
    simp only [hR, v, transpose_fromRows, fromCols_mulVec_sumElim, transpose_sub, transpose_mul,
      transpose_transpose, hPT, e, mulVec_add, mulVec_sub, mulVec_neg, mulVec_mulVec,
      Matrix.mul_sub, ← Matrix.mul_assoc, hPL, hGw, hGv]
    abel
  -- the two halves of the form
  have hquad : v ⬝ᵥ (((-R) * P⁻¹ * (-R)ᵀ) *ᵥ v) = e ⬝ᵥ (P *ᵥ e) := by
    simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hRv, dotProduct_mulVec, ← mulVec_transpose, hRv,
      mulVec_mulVec, inv_mul_of_invertible, one_mulVec, dotProduct_comm]
  -- the diagonal blocks give `γ θᵀPθ + ‖D_xH_w s₁‖² + ‖D_yH_v s₂‖²`
  have hTLv : v ⬝ᵥ ((-TL) *ᵥ v) = γ * (θ ⬝ᵥ (P *ᵥ θ)) + (Gw *ᵥ s₁) ⬝ᵥ (Gw *ᵥ s₁) +
      (Gv *ᵥ s₂) ⬝ᵥ (Gv *ᵥ s₂) := by
    have hG : ∀ {k r : ℕ} (G : Mat ℝ k r) (s : Vec ℝ r), s ⬝ᵥ ((Gᵀ * G) *ᵥ s) =
        (G *ᵥ s) ⬝ᵥ (G *ᵥ s) := fun G s => by
      rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp only [hTL, v, neg_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      zero_mulVec, add_zero, zero_add, dotProduct_neg, sumElim_dotProduct_sumElim, neg_neg,
      smul_mulVec, dotProduct_smul, smul_eq_mul, mulVec_neg, neg_dotProduct, hG]
    simp only [neg_zero, add_zero, dotProduct_neg, hG]
    ring
  have hq := (posDef_iff_dotProduct_mulVec.mp hS).2
  have hpsd : 0 ≤ v ⬝ᵥ ((-TL - (-R) * P⁻¹ * (-R)ᵀ) *ᵥ v) := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hq hv).le
  rw [sub_mulVec, dotProduct_sub, hTLv, hquad] at hpsd
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
