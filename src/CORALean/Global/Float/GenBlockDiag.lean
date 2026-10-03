import CORALean.Global.Float.SoundFloatArithmetic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Block-diagonal generator matrices

CORA's `blkdiag(G₁, G₂)`: the first block's rows carry `G₁` on the first columns and `0` after,
the second block's rows `0` and then `G₂`. Entries are copied or `zero`, so nothing rounds.
The columns, read as real vectors, are the two operands' columns padded with zeros on the other
side, which is what a Cartesian product of generator representations needs.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] {n₁ n₂ h₁ h₂ : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def genBlockDiag (A : Mat 𝕋 n₁ h₁) (B : Mat 𝕋 n₂ h₂) : Mat 𝕋 (n₁ + n₂) (h₁ + h₂) :=
  Fin.append (fun i => Fin.append (A i) fun _ => zero) (fun i => Fin.append (fun _ => zero) (B i))

/-- A column of the first block, read as reals, is the operand's column padded below with zeros. -/
theorem toReal_genBlockDiag_left [SoundFloatArithmetic 𝕋] (A : Mat 𝕋 n₁ h₁) (B : Mat 𝕋 n₂ h₂)
    (l : Fin h₁) :
    (fun i => toReal (genBlockDiag A B i (Fin.castAdd h₂ l))) =
      Fin.append (fun i => toReal (A i l)) (fun _ : Fin n₂ => (0 : ℝ)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [genBlockDiag, toReal_zero]

/-- A column of the second block, read as reals, is the operand's column padded above with zeros. -/
theorem toReal_genBlockDiag_right [SoundFloatArithmetic 𝕋] (A : Mat 𝕋 n₁ h₁) (B : Mat 𝕋 n₂ h₂)
    (l : Fin h₂) :
    (fun i => toReal (genBlockDiag A B i (Fin.natAdd h₁ l))) =
      Fin.append (fun _ : Fin n₁ => (0 : ℝ)) (fun i => toReal (B i l)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [genBlockDiag, toReal_zero]

/-- Stacked centres, read as reals, are the stacked readings. -/
theorem toRealVec_append [SoundFloatArithmetic 𝕋] (c₁ : Vec 𝕋 n₁) (c₂ : Vec 𝕋 n₂) :
    toRealVec (Fin.append c₁ c₂) = Fin.append (toRealVec c₁) (toRealVec c₂) := by
  refine funext (Fin.addCases (fun i => ?_) (fun i => ?_)) <;>
    simp only [toRealVec, Fin.append_left, Fin.append_right]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
