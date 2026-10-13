import CORALean.Global.Float.SoundFloatArithmetic
import Mathlib.Data.Matrix.Mul

/-!
# A matrix product rounded down is close to the exact one

Entry by entry, off by at most `matMulDiff`, the gap between the two directed roundings. The
matrix counterpart of `matMul_close`, which reads the product a column at a time.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n k m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.matMulDown_close (A : Mat 𝕋 n k) (B : Mat 𝕋 k m) (i : Fin n) (j : Fin m) :
    |(toRealMat A * toRealMat B) i j - toReal (matMulDown A B i j)|
      ≤ toReal (matMulDiff A B i j) := by -- --- PROOF ---
  -- the exact entry is bracketed by the two roundings, and their gap rounds up
  have hlo : toReal (matMulDown A B i j) ≤ ∑ r, toReal (A i r) * toReal (B r j) :=
    dotDown_le (A i) (fun r => B r j)
  have hhi : ∑ r, toReal (A i r) * toReal (B r j) ≤ toReal (matMulUp A B i j) :=
    le_dotUp (A i) (fun r => B r j)
  have hgap := sub_le_subUp (matMulUp A B i j) (matMulDown A B i j)
  have hex : (toRealMat A * toRealMat B) i j = ∑ r, toReal (A i r) * toReal (B r j) := by
    simp only [Matrix.mul_apply, toRealMat]
  show _ ≤ toReal (subUp (matMulUp A B i j) (matMulDown A B i j))
  rw [hex, abs_le]
  exact ⟨by linarith, by linarith⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
