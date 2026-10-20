module

public import CORALean.ContSet.Interval.Float.Operations.Kron
public import CORALean.ContSet.Interval.Real.Theorems.KronOuter
public import CORALean.ContSet.Interval.Real.Theorems.MemMat
public import CORALean.ContSet.Interval.Float.Theorems.MulLoLe
public import CORALean.ContSet.Interval.Float.Theorems.LeMulHi

@[expose] public section

/-!
# `Interval.kron` holds every Kronecker product of members

The real layer has proved the statement for the nominal boxes; what is left is that every corner
product rounds the right way, `mulLo_le` and `le_mulHi`, exactly as `matMul_outer` does.

## Inputs
* `I` – left interval matrix
* `J` – right interval matrix
* `A` – member of the left matrix
* `B` – member of the right matrix

## Hypotheses
* `hA` – `A` lies in `I`
* `hB` – `B` lies in `J`

## Conclusion
* the Kronecker product of `A` and `B` lies in the result
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Kronecker FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n p q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.kron_outer {I : Interval (Mat 𝕋 m n)} {J : Interval (Mat 𝕋 p q)}
    {A : Mat ℝ m n} {B : Mat ℝ p q} (hA : A ∈ I.construct) (hB : B ∈ J.construct) : -- --- CONCL ---
    Matrix.reindex finProdFinEquiv finProdFinEquiv (A ⊗ₖ B) ∈
      (Interval.kron I J).construct := by -- --- PROOF ---
  have h := Real.Interval.mem_mat_iff.mp (Real.Interval.kron_outer hA hB)
  refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
  have h' := h i j
  simp only [Real.Interval.kron, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
    Interval.nominal, RealImage.realImage, toRealMat] at h'
  simp only [Interval.kron, Interval.nominal, RealImage.realImage, toRealMat,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  exact ⟨le_trans (Interval.mulLo_le _ _ _ _) h'.1, le_trans h'.2 (Interval.le_mulHi _ _ _ _)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
