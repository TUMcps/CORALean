import CORALean.NN.Operations.Raise

/-!
# The neuron-wise refinement step

[1, Def. 4.4]: neuron `j` of layer `l` moves up an order, and nothing else
moves. One `raise` at a single coordinate.

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


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One neuron-wise step [1, Def. 4.4]: neuron `j` of layer `l` moves up an
order, and nothing else moves. -/
def Schedule.refine (sch : Schedule) (l j : ℕ) : Schedule :=
  Schedule.raise sch l fun i => if i = j then 1 else 0

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
