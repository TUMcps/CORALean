import CORALean.NN.Layers.Operations.TapMat
import CORALean.NN.Layers.Theorems.ToRealTapEntry

/-!
# A stencil matrix reads back exactly

An equality with no hypothesis: the stored stencil denotes the stencil over ℝ at the weights
that were read in, entry for entry, `toReal_tapEntry` row by row.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps Float.SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m k : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem toRealMat_tapMat (tap : Fin m → Fin k → Fin n) (w : Fin m → Fin k → 𝕋) :
    toRealMat (tapMat tap w) = tapMat tap fun j l => toReal (w j l) := by
  funext j i
  exact toReal_tapEntry (tap j) (w j) i

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
