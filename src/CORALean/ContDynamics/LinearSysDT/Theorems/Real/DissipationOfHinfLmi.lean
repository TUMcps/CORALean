module

public import CORALean.ContDynamics.LinearSysDT.Definitions.HinfLmi
public import CORALean.Global.PosDefSchurComplement
public import CORALean.Global.ExistsPosLeOfPosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# The dissipation inequality of the `H∞` design

The step of the proof of [1, Thm. 1] from its Eq. 16 to its Eq. 17: if `P ≻ 0` and the
inequality Eq. 16 holds, then at `L = P⁻¹ Y`, `A_e = A - LC`, for every `e`, `w`, `v`
`(A_e e + E w - L F v)ᵀ P (A_e e + E w - L F v) + eᵀe - eᵀPe - γ²(wᵀw + vᵀv) ≤ -ε (eᵀe + wᵀw + vᵀv)`
for some `ε > 0`. The Schur complement of the block `P` (`posDef_schur_of_fromBlocks`) is its
Eq. 18, and a positive definite form has a margin (`exists_pos_le_of_posDef`); that margin is
what makes the `H∞` bound of [1, Thm. 1] strict.

## Inputs
* `A` – state matrix
* `C` – output matrix
* `E` – disturbance matrix
* `F` – noise matrix
* `P` – Lyapunov matrix
* `Y` – gain variable
* `γ` – attenuation level

## Hypotheses
* `hP` – Lyapunov matrix positive definite
* `h` – the design inequality holds

## Conclusion
* the dissipation inequality holds with a positive margin

## References

* [1] W. Tang, Z. Wang, Y. Wang, T. Raïssi and Y. Shen. "Interval estimation methods for
      discrete-time linear time-invariant systems". IEEE Transactions on Automatic Control,
      64(11):4717-4724, 2019.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nw nv : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.dissipation_of_hinfLmi (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ n nw)
    (F : Mat ℝ ny nv) (P : Mat ℝ n n) (Y : Mat ℝ n ny) (γ : ℝ) (hP : P.PosDef)
    (h : LinearSysDT.HinfLmi A C E F P Y γ) : -- --- CONCL ---
    ∃ ε > 0, ∀ (a : Vec ℝ n) (b : Vec ℝ nw) (c : Vec ℝ nv),
      let q := (A - P⁻¹ * Y * C) *ᵥ a + E *ᵥ b - (P⁻¹ * Y * F) *ᵥ c
      q ⬝ᵥ (P *ᵥ q) + a ⬝ᵥ a - a ⬝ᵥ (P *ᵥ a) - γ ^ 2 * (b ⬝ᵥ b + c ⬝ᵥ c) ≤
        -ε * (a ⬝ᵥ a + b ⬝ᵥ b + c ⬝ᵥ c) := by -- --- PROOF ---
  haveI : Invertible P := hP.isUnit.invertible
  set TL : Matrix (Fin n ⊕ (Fin nw ⊕ Fin nv)) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromBlocks (1 - P) 0 0 (fromBlocks (-(γ ^ 2) • 1) 0 0 (-(γ ^ 2) • 1)) with hTL
  set R : Matrix (Fin n) (Fin n ⊕ (Fin nw ⊕ Fin nv)) ℝ :=
    fromCols (P * A - Y * C) (fromCols (P * E) (-(Y * F))) with hR
  -- Eq. 18 of [1, Thm. 1]: the Schur complement of the block `P`
  have hneg : -(fromBlocks TL Rᵀ R (-P)) = fromBlocks (-TL) (-Rᵀ) (-Rᵀ)ᵀ P := by
    rw [fromBlocks_neg, transpose_neg, transpose_transpose, neg_neg]
  have hS := posDef_schur_of_fromBlocks (-TL) (-Rᵀ) hP (hneg ▸ h)
  obtain ⟨ε, hε, hle⟩ := exists_pos_le_of_posDef _ hS
  refine ⟨ε, hε, fun a b c => ?_⟩
  intro q
  have hPT : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian.eq
  -- `R (a, b, c) = P q`, the gain `L = P⁻¹ Y` undone
  have hRq : R *ᵥ Sum.elim a (Sum.elim b c) = P *ᵥ q := by
    have hPL : P * (P⁻¹ * Y) = Y := by
      rw [← Matrix.mul_assoc, mul_inv_of_invertible, Matrix.one_mul]
    simp only [hR, q, fromCols_mulVec_sumElim, mulVec_add, mulVec_sub, mulVec_mulVec,
      Matrix.mul_sub, ← Matrix.mul_assoc, hPL, neg_mulVec]
    abel
  -- the Schur term is `qᵀ P q`
  have hquad : Sum.elim a (Sum.elim b c) ⬝ᵥ ((-Rᵀ * P⁻¹ * (-Rᵀ)ᵀ) *ᵥ Sum.elim a (Sum.elim b c))
      = q ⬝ᵥ (P *ᵥ q) := by
    simp only [transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hRq, dotProduct_mulVec, vecMul_transpose, hRq,
      mulVec_mulVec, inv_mul_of_invertible, one_mulVec, dotProduct_comm]
  -- the diagonal blocks give `aᵀ(P - I)a + γ²(bᵀb + cᵀc)`
  have hTLq : Sum.elim a (Sum.elim b c) ⬝ᵥ ((-TL) *ᵥ Sum.elim a (Sum.elim b c)) =
      a ⬝ᵥ (P *ᵥ a) - a ⬝ᵥ a + γ ^ 2 * (b ⬝ᵥ b + c ⬝ᵥ c) := by
    simp only [hTL, neg_mulVec, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
      zero_mulVec, add_zero, zero_add, dotProduct_neg, sumElim_dotProduct_sumElim, sub_mulVec,
      one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, neg_smul,
      dotProduct_neg]
    ring
  have hξ := hle (Sum.elim a (Sum.elim b c))
  rw [sub_mulVec, dotProduct_sub, hTLq, hquad, sumElim_dotProduct_sumElim,
    sumElim_dotProduct_sumElim] at hξ
  linarith

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
