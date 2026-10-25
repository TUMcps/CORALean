module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
public import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexExact

@[expose] public section

/-!
# `sort` is exact

[1, Prop. 3.2] writes the sorted set down as an equality of representations and
says nothing about what it denotes, which is the part worth stating: the
permutation is applied to the generators and to their columns together, so the
sum is the same sum and no hypothesis on the operand is needed.

## Inputs
* `pZ` – polynomial zonotope

## Hypotheses
* none

## Conclusion
* sorting leaves the set unchanged

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural Network Verification
      using Sensitivity Analysis". Proceedings of the 26th ACM International Conference on Hybrid
      Systems: Computation and Control, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sort_exact (pZ : PolyZonotope α) : pZ.construct = pZ.sort.construct :=
  pZ.reindex_exact (PolyZonotope.sortPerm pZ.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
