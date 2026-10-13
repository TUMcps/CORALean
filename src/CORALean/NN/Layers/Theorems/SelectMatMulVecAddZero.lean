import CORALean.NN.Layers.Theorems.SelectMatMulVec

/-!
# A selection with a zero offset

`W x + 0` at a selection matrix `W` is the selection: the form an affine map takes when all
it does is pick coordinates, which is how a CAT function renames or reorders them. The zero is
stored as `zero`, which every scalar reads back exactly.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open scoped Matrix
open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem selectMat_mulVec_add_zero (sel : Fin m → Fin n) (x : Vec ℝ n) (j : Fin m) :
    ((toRealMat (selectMat (𝕋 := 𝕋) sel) *ᵥ x + toRealVec (fun _ => (zero : 𝕋)) : Vec ℝ m) j)
      = x (sel j) := by
  rw [Pi.add_apply, selectMat_mulVec]
  show _ + toReal (zero : 𝕋) = _
  rw [toReal_zero, add_zero]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
