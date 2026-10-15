module

public import CORALean.NN.Layers.Definitions.RootRelaxation
public import CORALean.NN.Layers.Theorems.OfMonotoneSound
public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The square root relaxation over ℝ is sound

`Real.sqrt` is monotone and the exact enclosure is sound, so `Relaxation.ofMonotone_sound` applies.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem rootRelaxation_sound : rootRelaxation.Sound Real.sqrt :=
  Relaxation.ofMonotone_sound (fun _ _ h => Real.sqrt_le_sqrt h) (enclosure_exact_sound _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
