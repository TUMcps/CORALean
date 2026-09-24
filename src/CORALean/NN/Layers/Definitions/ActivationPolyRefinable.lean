import CORALean.NN.Definitions.RefinableLayer
import CORALean.NN.Layers.Definitions.ActivationPoly
import CORALean.NN.Layers.Layer
import CORALean.NN.Layers.Operations.PolyRelaxationFamilyAtPattern
import CORALean.NN.Layers.Theorems.AtPatternSound
import CORALean.NN.Layers.Theorems.Real.ActivationPolySound
import CORALean.NN.Operations.RefinableLayerAtPattern
import CORALean.NN.Theorems.RefinableLayerAtPatternSound

/-!
# The exact polynomial activation layer as a refinable layer

The refinement loop's one interesting layer [1], at the exact polynomial zonotope: a family
reads an order pattern as one level per neuron, every level sound, so the schedule decides
precision alone. The neurons' orders differ, so their fits do; `atPattern` pads each to the
layer's largest degree, which is exact, so one coefficient list still serves. ℝ-only, the
enclosure being the exact layer's: this is the layer whose convergence is stated.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {σ : ℝ → ℝ} {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The activation layer of a sound family: one `σ`, one exact enclosure per pattern. -/
noncomputable def Layer.activationPolyRefinable (F : PolyRelaxationFamily ℝ) (hF : F.Sound σ) :
    RefinableLayer 𝒫𝒵 n n where
  eval x := fun i => σ (x i)
  enclose t := (Layer.activationPoly (F.atPattern t)).enclose
  enclose_outer t := (Layer.activationPoly_sound (F.atPattern_sound hF t)).enclose_outer

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
