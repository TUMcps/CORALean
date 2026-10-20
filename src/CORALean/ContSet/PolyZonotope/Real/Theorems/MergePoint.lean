module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSumEqZeroOfNotMemMerge
public import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumMergeKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.SumMonomialMerge

@[expose] public section

/-!
# `merge` moves no point

[1, Prop. 3.3] at one factor vector, and what `merge_exact` is assembled from:
`sum_monomial_merge` regroups the generator sum at `rep` and at the columns
`merge` keeps, and the two hypotheses it asks for are `col_rep` and
`fiberSum_eq_zero_of_notMem_merge`.

The center does not move, so the whole of it is that one sum.

## Inputs
* `pZ` – polynomial zonotope
* `a` – factor values

## Hypotheses
* none

## Conclusion
* merging leaves the point unchanged

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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

-- file-local: only `merge_point` below needs it
/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.aux_sum_merge (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ j : Fin pZ.merge.h,
          PolyZonotope.monomial pZ.merge.E a j • pZ.merge.G j := by -- --- PROOF ---
  rw [PolyZonotope.sum_monomial_merge pZ.E pZ.G a (PolyZonotope.rep pZ.E)
      (PolyZonotope.mergeKeep pZ.E) (PolyZonotope.col_rep pZ.E)
      fun j hj => PolyZonotope.fiberSum_eq_zero_of_notMem_merge pZ.E pZ.G hj,
    PolyZonotope.sum_mergeKeep]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.merge_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    pZ.merge.point a = pZ.point a :=
  congrArg (fun s => pZ.c + s) (PolyZonotope.aux_sum_merge pZ a).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
