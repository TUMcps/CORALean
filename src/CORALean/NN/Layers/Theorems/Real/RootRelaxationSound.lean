import CORALean.NN.Layers.Definitions.RootRelaxation
import CORALean.NN.Layers.Theorems.OfMonotoneSound
import CORALean.NN.Layers.Theorems.Real.EnclosureExactSound
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The square root relaxation over ℝ is sound

`Real.sqrt` is monotone and the exact enclosure is sound, so `Relaxation.ofMonotone_sound` applies.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem rootRelaxation_sound : rootRelaxation.Sound Real.sqrt :=
  Relaxation.ofMonotone_sound (fun _ _ h => Real.sqrt_le_sqrt h) (enclosure_exact_sound _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
