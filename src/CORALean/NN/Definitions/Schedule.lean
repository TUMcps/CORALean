module

public import CORALean.NN.Definitions.RefinableNetwork

@[expose] public section

/-!
# Schedules

A schedule is an order pattern per layer, read layer first and neuron second: layer `0` is the
network's first and the tail reads the schedule shifted. That is CORA's order pattern tuple
[1, Eq. 23], holding the refinement loop's state and nothing else.

Plain ℕ indices rather than a `Fin` per layer: a dependent schedule would need widths
`RefinableNetwork` does not carry. How a schedule is taken apart and put together — `head`, `tail`,
`cons` — and what it is *for* are `Operations/*.lean`, one file each.

## Inputs
* none

## Output
* order pattern per layer and neuron

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5.5
-- Written:       05-September-2026
-- Last update:   23-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One order pattern per layer, layer `0` first and neuron second. -/
abbrev Schedule := ℕ → ℕ → ℕ

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
