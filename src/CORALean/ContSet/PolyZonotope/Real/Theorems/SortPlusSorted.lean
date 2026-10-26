module

public import CORALean.ContSet.PolyZonotope.Real.Operations.SortPlus
public import CORALean.ContSet.PolyZonotope.Real.Theorems.MergeSorted
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SortSorted

@[expose] public section

/-!
# `sortPlus` returns a sorted matrix

The second half of [1, Prop. 3.4]'s conclusion, *`P̂Z` is regular and sorted*:
`sort` sorts and `merge` keeps it sorted, so no hypothesis on the operands is
needed — which is the difference from [1], where they are assumed sorted so
that the sorting can be an `m`-way merge.

Of regularity only `merge_col_injective` holds, and it applies here unchanged,
`sortPlus` being a `merge`; the all-zero column `Merge.lean` describes survives
this too.

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

omit [Module ℝ α] in
theorem PolyZonotope.sortPlus_isSorted (pZ₁ pZ₂ : PolyZonotope α) (hp : pZ₁.p = pZ₂.p) :
    PolyZonotope.IsSorted (pZ₁.sortPlus pZ₂ hp).E :=
  PolyZonotope.merge_isSorted (pZ₁.exactPlus pZ₂ hp).sort_isSorted

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
