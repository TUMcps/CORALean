module

public import CORALean.Global.Tensor
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# A neuron's approximation error, biased towards earlier layers

The paper's heuristic [1, Def. 4.10]: neuron `j`'s own approximation error, scaled down the further
into the network layer `l` sits — later layers depend on earlier ones having been resolved well. `l
+ 1` rather than the paper's bare `k`: CORALean numbers a network's refinable layers from `0`, where
the paper's `k` never reaches, and dividing there would make the first layer the one the bias falls
hardest on. Nothing here is proved and nothing here can be wrong: `encloseAt_outer` holds at every
schedule, so this only decides where the next order is spent.

## Inputs
* `d` – approximation errors of the neurons
* `l` – layer index
* `j` – neuron index

## Output
* the neuron's error divided by the layer index plus one

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       11-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Neuron `j`'s rank under `σ`-Approximation-Error [1, Def. 4.9]: the
error its own relaxation leaves, and nothing else. -/
def aux_refinementRankApproxError (d : Vec ℝ n) (j : Fin n) : ℝ := |d j|


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s rank under `σ`-Layer-Bias [1, Def. 4.10]: its own
approximation error, divided by `l + 1`. -/
noncomputable def refinementRankLayerBias (d : Vec ℝ n) (l : ℕ) (j : Fin n) : ℝ :=
  aux_refinementRankApproxError d j / ((l : ℝ) + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
