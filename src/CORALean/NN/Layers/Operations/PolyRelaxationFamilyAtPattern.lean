import CORALean.NN.Layers.Operations.PolyRelaxationFamilyDegOf
import CORALean.NN.Layers.Operations.PolyRelaxationPadTo

/-!
# A layer's abstraction at an order pattern

Each neuron's own fit at its own level, padded to the common degree, which is exact.
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

/-- Each neuron's own fit at its own level, padded to the common degree. -/
def PolyRelaxationFamily.atPattern (F : PolyRelaxationFamily 𝕋) (t : OrderPattern n) :
    LayerRelaxation 𝕋 n (F.degOf t) :=
  fun i => (F.rel (t i)).padTo (F.degOf t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
