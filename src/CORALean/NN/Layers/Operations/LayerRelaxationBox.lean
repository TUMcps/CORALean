import CORALean.NN.Layers.Definitions.PolyRelaxation
import CORALean.ContSet.Interval.Float.Interval

/-!
# The box a layer's fits leave

Each neuron's deviation from its own polynomial is confined to `[-error, error]`: centred at
zero, where `neg` is exact, so this box rounds nowhere.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The box each neuron's deviation from its own polynomial is confined to. -/
def LayerRelaxation.box (P : LayerRelaxation 𝕋 n m) (I : Interval 𝕋 n) : Interval 𝕋 n where
  inf := fun i => neg ((P i).error (I.inf i) (I.sup i))
  sup := fun i => (P i).error (I.inf i) (I.sup i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
