import CORALean.ContSet.HPolytope.Float.Operations.PadRight
import CORALean.Global.Block

/-!
# A padded row reads only the block it came from, on the right
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}

-- and the same on the right block
theorem HPolytope.mulVec_padRight {m : ℕ} (M : Mat 𝕋 m n₂) (x : Vec ℝ (n₁ + n₂)) (i : Fin m) :
    (toRealMat (fun i' => Fin.append (fun _ : Fin n₁ => FloatOps.zero) (M i')) *ᵥ x) i
      = (toRealMat M *ᵥ blockRight n₁ n₂ x) i := by
  show ∑ k : Fin (n₁ + n₂), toReal (Fin.append (fun _ => FloatOps.zero) (M i) k) * x k
      = ∑ k, toReal (M i k) * x (Fin.natAdd n₁ k)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
    Finset.sum_const_zero, zero_add]

end CORALean.Float
