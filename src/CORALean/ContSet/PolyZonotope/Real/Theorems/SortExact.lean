import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReindexExact

/-!
# `sort` is exact

[1, Prop. 3.2] writes the sorted set down as an equality of representations and
says nothing about what it denotes, which is the part worth stating: the
permutation is applied to the generators and to their columns together, so the
sum is the same sum and no hypothesis on the operand is needed.

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sort_exact (pZ : PolyZonotope α) : pZ.construct = pZ.sort.construct :=
  pZ.reindex_exact (PolyZonotope.sortPerm pZ.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
