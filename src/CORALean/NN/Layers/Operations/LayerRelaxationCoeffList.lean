module

public import CORALean.NN.Layers.Operations.LayerRelaxationCoeffVec

@[expose] public section

/-!
# A layer's fits as an evaluation takes them

The coefficient vectors as `PolyZonotope.evalPoly` takes them, lowest degree first.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The coefficient vectors, lowest degree first. -/
def LayerRelaxation.coeffList (P : LayerRelaxation 𝕋 n m) (I : Interval (Vec 𝕋 n)) :
    List (Vec 𝕋 n) := List.ofFn (P.coeffVec I)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
