import CORALean.ContSet.HPolytope.Float.Theorems.MemConstruct

/-!
# A row carrying one trailing column reads the parameter it holds
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {N m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

-- a trailing column adds its entry against the coefficient the block holds
theorem HPolytope.mulVec_append_last (A : Mat 𝕋 m N) (d : Vec 𝕋 m) (u : Vec ℝ N) (r : ℝ)
    (i : Fin m) :
    (toRealMat (fun i' => Fin.append (A i') fun _ : Fin 1 => d i')
        *ᵥ Fin.append u fun _ : Fin 1 => r) i
      = (toRealMat A *ᵥ u) i + toReal (d i) * r := by -- --- PROOF ---
  show ∑ k : Fin (N + 1), toReal (Fin.append (A i) (fun _ => d i) k)
      * Fin.append u (fun _ : Fin 1 => r) k = _
  rw [Fin.sum_univ_add, Fin.sum_univ_one]
  simp only [Fin.append_left, Fin.append_right]
  rfl

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
