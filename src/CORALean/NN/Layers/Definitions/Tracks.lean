module

public import CORALean.ContSet.Zonotope.Float.Definitions.Tracks
public import CORALean.ContSet.Zonotope.Float.Instances
public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# A layer that keeps the generators of a zonotope in front

On zonotopes the image of a layer has the generators of its argument first, each mapped, and
fresh ones for what the layer adds; a layer tracks `f` when its image of every zonotope tracks `f`
over it (`Zonotope.Tracks`). It is what the closed loop asks of a network to share the dependence
of the output on the state, which `Layer.Encloses` does not say.

## Inputs
* `L` – layer
* `f` – function

## Output
* proposition that the layer tracks the function
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float
open scoped CORALean.Float

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Layer.Tracks (L : Layer 𝒵[𝕋] n m) (f : Vec ℝ n → Vec ℝ m) : Prop :=
  ∀ X : Zonotope (Vec 𝕋 n), X.Tracks (L.enclose X) f

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
