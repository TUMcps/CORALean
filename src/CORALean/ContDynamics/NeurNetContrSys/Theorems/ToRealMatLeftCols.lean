module

public import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
public import CORALean.ContDynamics.NeurNetContrSys.Operations.Basic

@[expose] public section

/-!
# `leftCols` commutes with reading a matrix into ℝ

The left block of columns of `B`, read into ℝ, is the same block of `B` read into ℝ: a
column selection and `toRealMat` act on different things. The discrete-time loop keeps `B_nn` and
`B_ext` in the plant's scalar, its theorems read them in ℝ.

## Inputs
* `𝕋` – scalar type
* `n` – row count
* `M` – column count
* `m` – split column
* `B` – matrix

## Hypotheses
* `hm` – split column fits

## Conclusion
* selecting the left columns commutes with reading into ℝ
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       15-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Scalar


-- =======================================  MAIN THEOREM  ======================================= --

theorem toRealMat_leftCols {𝕋 : Type} [Scalar 𝕋] {n M m : ℕ} (hm : m ≤ M) (B : Mat 𝕋 n M) :
    toRealMat (leftCols hm B) = leftCols hm (toRealMat B) := by
  funext i j
  simp only [leftCols, Matrix.of_apply, toRealMat_apply]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
