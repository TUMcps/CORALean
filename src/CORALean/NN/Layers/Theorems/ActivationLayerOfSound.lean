import CORALean.NN.Layers.Instances
import CORALean.NN.Layers.Operations.ActivationLayerOf

/-!
# An activation layer is sound at the `σ` it was built from

`Layer.activation_sound`, stated at `Enclose.toLayer` of the kind: the form a network's
`Sound` relation asks for, so a caller does not unfold the instance to use it.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {𝕋 : Type} [Float.FloatOps 𝕋] [Float.SoundFloatArithmetic 𝕋]
  {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, Plus (S n) (Vec ℝ n)]
  [Mtimes (Mat 𝕋) S] [Float.IntervalOuter S 𝕋] [Float.OfInterval S 𝕋] {n : ℕ} {σ : ℝ → ℝ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ActivationLayer.of_sound {R : Relaxation 𝕋} (hR : R.Sound σ) :
    (Enclose.toLayer (S := S) (ActivationLayer.of (n := n) hR)).Sound fun x i => σ (x i) :=
  Layer.activation_sound hR

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
