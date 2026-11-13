module

public import CORALean.NN.Layers.Operations.Activation
public import CORALean.NN.Layers.Operations.PolyBoxIndep

@[expose] public section

/-!
# The activation layer with the error in the independent generators

CORA's `evaluatePolyZonotope` with `add_approx_error_to_GI`: `Layer.activation` on a polynomial
zonotope, the box of the relaxation held by independent generators (`OfInterval.polyIndep`) and
not by the error box. The slope, offset and error are the relaxation's, so the sets differ in
the representation of the error only: the next linear layer sees generators and not a box.

## Inputs
* `R` – relaxation of the activation

## Output
* layer applying the relaxation and appending the error to `GI`
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `Layer.activation` on a polynomial zonotope with the box of the relaxation in `GI`. -/
def Layer.activationGI (R : Relaxation 𝕋) : Layer 𝒫𝒵[𝕋] n n :=
  letI : OfInterval 𝒫𝒵[𝕋] 𝕋 := OfInterval.polyIndep
  Layer.activation R

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
