module

public import CORALean.NN.Definitions.RefinableLayer
public import CORALean.NN.Layers.Definitions.ActivationPoly
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.PolyRelaxationFamilyAtPattern
public import CORALean.NN.Layers.Theorems.AtPatternSound
public import CORALean.NN.Layers.Theorems.Real.ActivationPolySound
public import CORALean.NN.Operations.RefinableLayerAtPattern
public import CORALean.NN.Theorems.RefinableLayerAtPatternSound

@[expose] public section

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

-- Authors:       Claude Opus 5.5
-- Written:       06-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


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
