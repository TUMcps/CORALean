module

public import CORALean.ContSet.HPolytope.Float.Operations.PadRight
public import CORALean.Global.Block

@[expose] public section

/-!
# A padded row reads only the block it came from, on the right
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n₁ n₂ : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- and the same on the right block
theorem HPolytope.mulVec_padRight {m : ℕ} (M : Mat 𝕋 m n₂) (x : Vec ℝ (n₁ + n₂)) (i : Fin m) :
    (toRealMat (fun i' => Fin.append (fun _ : Fin n₁ => FloatOps.zero) (M i')) *ᵥ x) i
      = (toRealMat M *ᵥ blockRight n₁ n₂ x) i := by -- --- PROOF ---
  show ∑ k : Fin (n₁ + n₂), toReal (Fin.append (fun _ => FloatOps.zero) (M i) k) * x k
      = ∑ k, toReal (M i k) * x (Fin.natAdd n₁ k)
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, toReal_zero, zero_mul,
    Finset.sum_const_zero, zero_add]

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
