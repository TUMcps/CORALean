module

public import CORALean.NN.Operations.Raise

@[expose] public section

/-!
# The neuron-wise refinement step

[1, Def. 4.4]: neuron `j` of layer `l` moves up an order, and nothing else
moves. One `raise` at a single coordinate.

## Inputs
* `sch` – schedule of order patterns
* `l` – layer index
* `j` – neuron index

## Output
* schedule with the neuron's order raised by one

## References

* [1] [T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control,
      2023.](../../../../references/2023/ladner-hscc-abstraction-refinement.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One neuron-wise step [1, Def. 4.4]: neuron `j` of layer `l` moves up an
order, and nothing else moves. -/
def Schedule.refine (sch : Schedule) (l j : ℕ) : Schedule :=
  Schedule.raise sch l fun i => if i = j then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
