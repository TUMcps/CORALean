import CORALean.Global.Tensor

/-!
# A neuron's share of the output error

The paper's per-neuron weight [1, Eq. 28]: a neuron's column of the
backpropagated Jacobian, summed in magnitude, against the error its own
relaxation leaves. `Operations.RefineWorst` sums it into a layer's rank and
`Operations.RefineWorstNeurons` reads it unaggregated — the same quantity
ranks both rules, only the aggregate differs.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Neuron `j`'s share of the output's error: its column of the sensitivity,
summed in magnitude, against the error its own relaxation leaves. -/
def refinementRank (J : Mat ℝ m n) (d : Vec ℝ n) (j : Fin n) : ℝ :=
  (∑ i, |J i j|) * |d j|

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
