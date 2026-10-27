module

public import CORALean.NN.Definitions.RefinableLayer
public import CORALean.NN.Layers.Definitions.PolyRelaxation
public import CORALean.NN.Layers.Layer

@[expose] public section

/-!
# The degree a whole layer is read at

The largest any of its neurons asks for, at an order pattern [1, Eq. 23], which padding lifts
the others to.

## Inputs
* `F` – family of polynomial relaxations
* `t` – order pattern of the layer

## Output
* largest degree any neuron of the layer asks for

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Float Float.FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The largest degree any neuron of the layer asks for. -/
def PolyRelaxationFamily.degOf (F : PolyRelaxationFamily 𝕋) (t : OrderPattern n) : ℕ :=
  Finset.univ.sup fun i => F.deg (t i)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
