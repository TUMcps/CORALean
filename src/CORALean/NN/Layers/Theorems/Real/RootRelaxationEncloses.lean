module

public import CORALean.NN.Layers.Definitions.RootRelaxation
public import CORALean.NN.Layers.Theorems.OfMonotoneEncloses
public import CORALean.NN.Layers.Theorems.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The square root relaxation over ℝ is sound

`Real.sqrt` is monotone and the exact enclosure is sound, so `Relaxation.ofMonotone_encloses`
applies.

## Inputs
* none

## Hypotheses
* none

## Conclusion
* the relaxation is sound for the square root
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem rootRelaxation_encloses : rootRelaxation.Encloses Real.sqrt :=
  Relaxation.ofMonotone_encloses (fun _ _ h => Real.sqrt_le_sqrt h) (enclosure_exact_encloses _)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
