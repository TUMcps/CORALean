module

public import CORALean.NN.Operations.RefinementRankApproxError

@[expose] public section

/-!
# A neuron's approximation error, biased towards earlier layers

The paper's heuristic [1, Def. 4.10]: neuron `j`'s own approximation error,
scaled down the further into the network layer `l` sits — later layers
depend on earlier ones having been resolved well. `l + 1` rather than the
paper's bare `k`: CORALean numbers a network's refinable layers from `0`,
where the paper's `k` never reaches, and dividing there would make the
first layer the one the bias falls hardest on rather than the one it
leaves alone.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer`
holds at every schedule, so this only decides where the next order is
spent, same as `refinementRank`.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s rank under `σ`-Layer-Bias [1, Def. 4.10]: its own
approximation error, divided by `l + 1`. -/
noncomputable def refinementRankLayerBias (d : Vec ℝ n) (l : ℕ) (j : Fin n) : ℝ :=
  refinementRankApproxError d j / ((l : ℝ) + 1)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
