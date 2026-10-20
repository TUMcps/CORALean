module

public import CORALean.NN.Layers.Instances
public import CORALean.NN.Layers.Operations.ActivationLayerOf

@[expose] public section

/-!
# An activation layer is sound at the `σ` it was built from

`Layer.activation_encloses`, stated at `Enclose.toLayer` of the kind: the form a network's
`Sound` relation asks for, so a caller does not unfold the instance to use it.

## Inputs
* `R` – relaxation of the activation

## Hypotheses
* `hR` – relaxation is sound for the activation

## Conclusion
* the layer built from the relaxation encloses the activation coordinatewise
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ActivationLayer.of_encloses {R : Relaxation 𝕋} (hR : R.Sound σ) :
    (Enclose.toLayer (S := S) (ActivationLayer.of (n := n) hR)).Encloses fun x i => σ (x i) :=
  Layer.activation_encloses hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
