module

public import CORALean.NN.Layers.Definitions.SoundLayer

@[expose] public section

/-!
# Packing a layer of any kind

A layer of any `Enclose` kind, of any universe, as a `SoundLayer`: the three fields read off
the instance, so nothing is lost but the kind.

## Inputs
* `Layer` – family of layer types
* `L` – layer

## Output
* sound layer wrapping the layer
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

universe u

namespace CORALean

variable {ContSet : ℕ → Type} [∀ n, ContSetLike (ContSet n) (Vec ℝ n)] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Enclose.pack {Layer : ℕ → ℕ → Type u} [Enclose Layer ContSet] (L : Layer n m) :
    SoundLayer ContSet n m where
  eval := Enclose.eval (ContSet := ContSet) L
  enclose := Enclose.enclose L
  enclose_outer := Enclose.enclose_outer L

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
