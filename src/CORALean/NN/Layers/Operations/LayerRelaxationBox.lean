module

public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.ContSet.Interval.Float.Interval

@[expose] public section

/-!
# The box a layer's fits leave

Each neuron's deviation from its own polynomial is confined to `[-error, error]`: centered at
zero, where `neg` is exact, so this box rounds nowhere.

## Inputs
* `P` – relaxation of every neuron
* `I` – box of the layer's input

## Output
* box confining each neuron's deviation from its polynomial
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

/-- The box each neuron's deviation from its own polynomial is confined to. -/
def LayerRelaxation.box (P : LayerRelaxation 𝕋 n m) (I : Interval (Vec 𝕋 n)) :
    Interval (Vec 𝕋 n) where
  inf := fun i => neg ((P i).error (I.inf i) (I.sup i))
  sup := fun i => (P i).error (I.inf i) (I.sup i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
