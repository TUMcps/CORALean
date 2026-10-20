module

public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Real.Theorems.DiagExact

@[expose] public section

/-!
# `Interval.diag` over floats is exact

`zero` reads as `0`, so the stored box denotes the exact layer's diagonal box of the reading.

## Inputs
* `I` – interval box

## Hypotheses
* none

## Conclusion
* the diagonal interval matrix is exactly the set of diagonal matrices
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Pointwise FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Interval.diag_exact (I : Interval (Vec 𝕋 n)) :
    I.diag.construct = Matrix.diagonal '' I.construct := by -- --- PROOF ---
  have h : I.diag.nominal = Real.Interval.diag I.nominal := by
    unfold Interval.nominal Interval.diag Real.Interval.diag
    congr 1 <;> funext i j <;> by_cases hij : i = j <;>
      simp [RealImage.realImage, toRealMat, toRealVec, hij, Matrix.diagonal_apply_ne, toReal_zero]
  show I.diag.nominal.construct = _
  rw [h]
  exact Real.Interval.diag_exact I.nominal

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
