module

public import CORALean.NN.Layers.Operations.ActivationGI
public import CORALean.NN.Layers.Theorems.ActivationEncloses

@[expose] public section

/-!
# The activation layer with the error in the independent generators is sound

`Layer.activation_encloses` at the `OfInterval` instance that puts the box in `GI`: that theorem
asks of the instance only that the set contains the box, which `Zonotope.ofIndep` of
`Interval.zonotope` does. The layers built on `Layer.activation` carry over by passing
this instance.

## Inputs
* `R` – relaxation of the activation

## Hypotheses
* `hR` – the relaxation is sound for the activation

## Conclusion
* the layer is sound for the activation coordinatewise
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       12-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet ContSetLike Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `σ` coordinatewise, the error in `GI`. -/
theorem Layer.activationGI_encloses {R : Relaxation 𝕋} (hR : R.Encloses σ) :
    (Layer.activationGI (n := n) R).Encloses (fun x i => σ (x i)) := by
  letI : OfInterval 𝒫𝒵[𝕋] 𝕋 := OfInterval.polyIndep
  exact Layer.activation_encloses hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
