module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Sort
public import CORALean.ContSet.PolyZonotope.Real.Operations.IsSorted

@[expose] public section

/-!
# `sort` sorts

The other half of [1, Prop. 3.2], and the one that does the work: the columns
of the result ascend lexicographically. `sort`'s exponent matrix is the
operand's read through `sortPerm`, so `colLex` of it is `colLex` composed with
`Tuple.sort` of that very function — which is what `Tuple.monotone_sort` is
about, and why the lexicographic order is carried in the type rather than in a
comparator.

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

omit [AddCommGroup α] [Module ℝ α] in
theorem PolyZonotope.sort_isSorted (pZ : PolyZonotope α) : PolyZonotope.IsSorted pZ.sort.E :=
  Tuple.monotone_sort (PolyZonotope.colLex pZ.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
