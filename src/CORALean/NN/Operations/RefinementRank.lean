import CORALean.NN.Operations.RefinementRankSensitivity

/-!
# A neuron's share of the output error

The paper's per-neuron weight [1, Def. 4.12]: `σ^(E·S)_k(j) = d_k(j)·s_k(j)`,
`Def. 4.9`'s approximation error times `Def. 4.11`'s sensitivity, so it is
literally `refinementRankSensitivity` scaled — the Euclidean norm of the neuron's
column of the backpropagated Jacobian, against the error its own relaxation
leaves. `Operations.RefineWorst` sums it into a layer's rank and
`Operations.RefineWorstNeurons` reads it unaggregated — the same quantity ranks
both rules, only the aggregate differs.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   18-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s share of the output's error, eq. (35)'s `σ^(E·S)_k(j)`:
`‖S_k(j,·)‖₂`, the Euclidean norm of its column of the sensitivity, times the
error `d_k(j)` its own relaxation leaves. -/
noncomputable def refinementRank (J : Mat ℝ m n) (d : Vec ℝ n) (j : Fin n) : ℝ :=
  refinementRankSensitivity J j * |d j|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
