module

public import CORALean.NN.Layers.Definitions.SoundLayer
public import CORALean.NN.Layers.Theorems.AffineTaylmEncloses
public import CORALean.NN.Layers.Theorems.Basic

@[expose] public section

/-!
# The affine layer on Taylor models as a packed layer

`Layer.affineTaylm` with the function it encloses, `x ↦ W x + b`, and the guarantee
(`Layer.affineTaylm_encloses`), the form `NeuralNetwork.layer` takes.

## Inputs
* `W` – weights
* `b` – bias

## Output
* the packed layer
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m d : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SoundLayer.affineTaylm (W : Mat 𝕋 m (n + 1)) (b : Vec 𝕋 m) :
    SoundLayer (TaylmArray 𝕋 d) (n + 1) m where
  eval := Erased.mk fun x => toRealMat W *ᵥ x + toRealVec b
  enclose := (Layer.affineTaylm W b).enclose
  enclose_outer s := by
    rw [Erased.out_mk]
    exact (Layer.affineTaylm_encloses W b).image_subset s

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
