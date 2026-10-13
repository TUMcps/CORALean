import CORALean.NN.Layers.Operations.TapMat

/-!
# The selection matrix

One input per output — the affine part a pooled window keeps. One stored `one` per row,
placed rather than computed, so it denotes the selection entry for entry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One input per output, which is the affine part a pooled window keeps. -/
def selectMat (sel : Fin m → Fin n) : Mat 𝕋 m n :=
  tapMat (fun (j : Fin m) (_ : Fin 1) => sel j) fun _ _ => one

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
