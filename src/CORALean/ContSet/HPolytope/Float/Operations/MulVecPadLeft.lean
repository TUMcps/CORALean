import CORALean.ContSet.HPolytope.Float.Operations.PadLeft
import CORALean.Global.Block

/-!
# A padded row reads only the block it came from, on the left
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- a padded row reads only the block it came from, the zero columns dropping out
theorem HPolytope.mulVec_padLeft {m : ℕ} (M : Mat 𝕋 m n₁) (x : Vec ℝ (n₁ + n₂)) (i : Fin m) :
    (toRealMat (fun i' => Fin.append (M i') fun _ : Fin n₂ => FloatOps.zero) *ᵥ x) i
      = (toRealMat M *ᵥ blockLeft n₁ n₂ x) i := by
  show ∑ k : Fin (n₁ + n₂), toReal (Fin.append (M i) (fun _ => FloatOps.zero) k) * x k
      = ∑ k, toReal (M i k) * x (Fin.castAdd n₂ k)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
