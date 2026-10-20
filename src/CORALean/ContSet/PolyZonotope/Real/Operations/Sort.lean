module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Reindex
public import CORALean.ContSet.PolyZonotope.Real.Operations.SortPerm

@[expose] public section

/-!
# `PolyZonotope.sort`

[1, Prop. 3.2]: the columns of the exponent matrix, and the generators they
scale, put in lexicographic order. Only the order of the dependent block
changes, so the set is untouched — `sort_exact` — and what is bought is that
equal columns are now adjacent.

[1] states it for a *regular* operand and reads the cost off the sorting.
Neither is a hypothesis here: a permutation of the summation index is exact
whatever the columns are, and regularity is what `merge` is for.

## Inputs
* `pZ` – polynomial zonotope

## Output
* polynomial zonotope with generators in sorted order

## References

* [1] T. Ladner and M. Althoff. "Automatic Abstraction Refinement in Neural
      Network Verification using Sensitivity Analysis". HSCC 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The dependent block reordered so that the exponent columns ascend. -/
noncomputable def PolyZonotope.sort (pZ : PolyZonotope α) : PolyZonotope α :=
  pZ.reindex (PolyZonotope.sortPerm pZ.E)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
