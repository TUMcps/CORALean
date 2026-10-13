import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmiPhi
import CORALean.ContDynamics.LinearSysDT.Definitions.HMinusLmiGain
import CORALean.Global.PosDefSchurComplementFirst

/-!
# The `H₋` inequality and its Schur complement

[1, Eq. 25], [1, Eq. 26]: for `Q ≻ 0`, `[Φ₁₁ Φ₁₂; ⋆ Φ₂₂] ≺ 0` (`LinearSysDT.HMinusLmiPhi`) iff
`[-Q  QA - QLC  -QLE; ⋆  -Q - CᵀMᵀMC  -CᵀMᵀME; ⋆  ⋆  -EᵀMᵀME + β²I] ≺ 0`
(`LinearSysDT.HMinusLmiGain`). The first row of Eq. 26 is `Q [(A - LC)  -LE]`, so the Schur
complement of `-Q` (`posDef_fromBlocks_first_iff`, on the negated matrix) is the lower block plus
`[(A - LC)  -LE]ᵀ Q [(A - LC)  -LE]`, which is Eq. 25.

## References

* [1] Y. Wang, M. Zhou, V. Puig, G. Cembrano and Z. Wang. "Zonotopic Fault Detection Observer
      with H− Performance". In Proc. of the 36th Chinese Control Conference (CCC),
      pp. 7230-7235, 2017.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix

variable {n ny nf : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSysDT.hMinusLmiPhi_iff_gain (A : Mat ℝ n n) (C : Mat ℝ ny n) (E : Mat ℝ ny nf)
    (L : Mat ℝ n ny) (Q : Mat ℝ n n) (M : Mat ℝ ny ny) (β : ℝ) (hQ : Q.PosDef) :
    LinearSysDT.HMinusLmiPhi A C E L Q M β ↔
      LinearSysDT.HMinusLmiGain A C E L Q M β := by -- --- PROOF ---
  haveI : Invertible Q := hQ.isUnit.invertible
  have hQT : Qᵀ = Q := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hQ.isHermitian.eq
  unfold LinearSysDT.HMinusLmiPhi LinearSysDT.HMinusLmiGain
  simp only
  -- the first row `R = Q K`, `K = [(A - LC)  -LE]`
  set K : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ := fromCols (A - L * C) (-(L * E)) with hK
  have hR : (fromCols (Q * A - Q * L * C) (-(Q * L * E)) : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ) =
      Q * K := by
    rw [hK, mul_fromCols, Matrix.mul_sub, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_assoc]
  set R : Matrix (Fin n) (Fin n ⊕ Fin nf) ℝ := Q * K with hRdef
  -- the negated matrix, and the Schur complement of its first block
  set D : Matrix (Fin n ⊕ Fin nf) (Fin n ⊕ Fin nf) ℝ :=
    fromBlocks (-Q - Cᵀ * Mᵀ * M * C) (-(Cᵀ * Mᵀ * M * E)) (-(Cᵀ * Mᵀ * M * E))ᵀ
      (-(Eᵀ * Mᵀ * M * E) + β ^ 2 • 1) with hD
  rw [hR]
  have hneg : -(fromBlocks (-Q) R Rᵀ D) = fromBlocks Q (-R) (-R)ᵀ (-D) := by
    rw [fromBlocks_neg, transpose_neg, neg_neg]
  rw [hneg, posDef_fromBlocks_first_iff Q (-R) (-D) hQ]
  -- the complement is `-Φ`: `Rᵀ Q⁻¹ R = Kᵀ Q K`, which is the block matrix of the `(A - LC)` terms
  have hRQ : (-R)ᵀ * Q⁻¹ * (-R) = Kᵀ * Q * K := by
    simp only [hRdef, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, transpose_mul, hQT,
      Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible]
  have hKQK : Kᵀ * Q * K = fromBlocks ((A - L * C)ᵀ * Q * (A - L * C))
      ((A - L * C)ᵀ * Q * (-(L * E))) ((A - L * C)ᵀ * Q * (-(L * E)))ᵀ
      ((L * E)ᵀ * Q * (L * E)) := by
    rw [hK, transpose_fromCols, Matrix.mul_assoc, mul_fromCols, fromRows_mul_fromCols]
    simp only [transpose_neg, transpose_mul, transpose_transpose, hQT, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg,
      Matrix.mul_assoc]
  have hcomp : -D - (-R)ᵀ * Q⁻¹ * (-R) = -(fromBlocks
      (-(Cᵀ * Mᵀ * M * C) + (A - L * C)ᵀ * Q * (A - L * C) - Q)
      ((A - L * C)ᵀ * Q * (-(L * E)) - Cᵀ * Mᵀ * M * E)
      ((A - L * C)ᵀ * Q * (-(L * E)) - Cᵀ * Mᵀ * M * E)ᵀ
      (β ^ 2 • 1 - Eᵀ * Mᵀ * M * E + (L * E)ᵀ * Q * (L * E))) := by
    rw [hRQ, hKQK, hD]
    -- compared entry by entry, the four blocks
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp <;> abel
  rw [hcomp]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
