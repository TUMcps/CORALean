import CORALean.Global.EuclideanNorm
import CORALean.Global.Tensor

/-!
# A neuron's own sensitivity

The paper's heuristic [1, Def. 4.11]: neuron `j`'s rank is the Euclidean
norm of its column of the sensitivity — how far it moves every output on
its own, with no approximation error weighed in. `refinementRank`
[1, Def. 4.12] is this scaled by the neuron's own approximation error,
which is how eq. (35) builds it.

Nothing here is proved and nothing here can be wrong: `encloseAt_outer`
holds at every schedule, so this only decides where the next order is
spent, same as `refinementRank`.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       11-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s rank under `σ`-Sensitivity [1, Def. 4.11]: the Euclidean
norm of its column of the sensitivity, `‖J(·, j)‖₂`. -/
noncomputable def refinementRankSensitivity (J : Mat ℝ m n) (j : Fin n) : ℝ :=
  ‖fun i => J i j‖₂

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
