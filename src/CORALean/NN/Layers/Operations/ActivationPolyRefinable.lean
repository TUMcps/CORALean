module

public import CORALean.NN.Definitions.RefinableLayer
public import CORALean.NN.Layers.Layer
public import CORALean.NN.Layers.Operations.ActivationPoly
public import CORALean.NN.Layers.Operations.Basic
public import CORALean.NN.Layers.Theorems.ActivationPolyEncloses
public import CORALean.NN.Layers.Theorems.Basic
public import CORALean.NN.Operations.RefinableLayerAtPattern
public import CORALean.NN.Theorems.Basic

@[expose] public section

/-!
# The polynomial activation layer as a refinable layer

A family reads an order pattern [1, Eq. 23] as one level per neuron, every level sound, so a
schedule changes nothing about correctness. `RefinableLayer` stores `eval`, so `σ` is an argument
here and nowhere below. Convergence is stated over ℝ only: at a machine scalar the representation's
own rounding is charged to an error box no refinement level touches.

## Inputs
* `F` – family of polynomial relaxations

## Hypotheses
* `hF` – the family is sound for the activation

## Output
* refinable layer with one enclosure per refinement level

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps
open scoped CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ} {σ : ℝ → ℝ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The activation layer of a family: one `σ`, one enclosure per pattern. -/
def Layer.activationPolyRefinable {F : PolyRelaxationFamily 𝕋} (hF : F.IsSound σ) :
    RefinableLayer 𝒫𝒵[𝕋] n n where
  eval x := fun i => σ (x i)
  enclose t := (Layer.activationPoly (F.atPattern t)).enclose
  enclose_outer t := (Layer.activationPoly_encloses (F.atPattern_sound hF t)).enclose_outer

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
