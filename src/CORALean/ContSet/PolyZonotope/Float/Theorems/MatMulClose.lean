import CORALean.ContSet.PolyZonotope.Float.Operations.Mtimes

/-!
# A stored column of a rounded matrix product is close to the exact one

Off by at most the gap between the two directed roundings.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}

/-- A stored column of a rounded product is off by at most the gap between the
two directed roundings. -/
theorem PolyZonotope.matMul_close {k : ℕ} (M : Mat 𝕋 m n) (A : Mat 𝕋 n k)
    (i : Fin m) (l : Fin k) :
    |(∑ r, toReal (M i r) * toReal (A r l)) - toReal (matMulDown M A i l)|
      ≤ toReal (matMulDiff M A i l) := by
  -- ascribed, so these are about `matMul*` rather than the `dot*` they unfold to
  have hlo : toReal (matMulDown M A i l) ≤ ∑ r, toReal (M i r) * toReal (A r l) :=
    dotDown_le (M i) (fun r => A r l)
  have hhi : ∑ r, toReal (M i r) * toReal (A r l) ≤ toReal (matMulUp M A i l) :=
    le_dotUp (M i) (fun r => A r l)
  have hgap := sub_le_subUp (matMulUp M A i l) (matMulDown M A i l)
  rw [abs_le]
  exact ⟨by simp only [matMulDiff]; linarith, by simp only [matMulDiff]; linarith⟩

end CORALean.Float
