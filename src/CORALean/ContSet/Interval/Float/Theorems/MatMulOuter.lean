import CORALean.ContSet.Interval.Float.Operations.MatMul
import CORALean.ContSet.Interval.Float.Theorems.MulBetweenCorners
import CORALean.ContSet.Interval.Real.Theorems.MatMulOuter
import CORALean.ContSet.Interval.Real.Theorems.MemMat

/-!
# `Interval.matMul` over-approximates every product of two matrices in the box

Nothing about products of matrices in boxes appears here — `Real` has already
proved that. The whole obligation is that each corner and each row sum rounds
the right way, exactly as `Mtimes.lean`'s does for a matrix acting on a box.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {m n p : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

theorem Interval.aux_matMul_outer_refines (A : Interval (Mat 𝕋 m n)) (B : Interval (Mat 𝕋 n p)) :
    (Real.Interval.matMul A.nominal B.nominal).construct
      ⊆ (Interval.matMul A B).construct := by -- --- PROOF ---
  intro X hX
  have hX' := Real.Interval.mem_mat_iff.mp hX
  refine Real.Interval.mem_mat_iff.mpr fun i j => ?_
  have h := hX' i j
  simp only [Real.Interval.matMul, Interval.nominal, RealImage.realImage, toRealMat] at h
  constructor
  · show toReal (sumDown fun k =>
        Interval.mulLo (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j)) ≤ X i j
    exact le_trans (sumDown_le_sum _)
      (le_trans (Finset.sum_le_sum fun k _ => Interval.mulLo_le _ _ _ _) h.1)
  · show X i j ≤ toReal (sumUp fun k =>
        Interval.mulHi (A.inf i k) (A.sup i k) (B.inf k j) (B.sup k j))
    exact le_trans h.2
      (le_trans (Finset.sum_le_sum fun k _ => Interval.le_mulHi _ _ _ _) (sum_le_sumUp _))


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.matMul_outer (A : Interval (Mat 𝕋 m n)) (B : Interval (Mat 𝕋 n p))
    {M : Mat ℝ m n} (hM : M ∈ A.construct) {N : Mat ℝ n p} (hN : N ∈ B.construct) :
    M * N ∈ (Interval.matMul A B).construct :=
  Interval.aux_matMul_outer_refines A B (Real.Interval.matMul_outer A.nominal B.nominal hM hN)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
