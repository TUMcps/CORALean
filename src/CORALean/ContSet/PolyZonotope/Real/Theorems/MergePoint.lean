module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import CORALean.ContSet.PolyZonotope.Real.Operations.MergeKeep
public import CORALean.ContSet.PolyZonotope.Real.Theorems.RepCongr
public import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
public import CORALean.ContSet.PolyZonotope.Real.Operations.Point
public import CORALean.ContSet.PolyZonotope.Real.Theorems.SumMonomialMerge

@[expose] public section

/-!
# `merge` moves no point

[1, Prop. 3.3] at one factor vector, and what `merge_exact` is assembled from:
`sum_monomial_merge` regroups the generator sum at `rep` and at the columns
`merge` keeps, and the two hypotheses it asks for are `col_rep` and
`aux_fiberSum_eq_zero_of_notMem_merge`.

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

section
variable {α : Type} [AddCommGroup α]

/-- A sum over the kept columns is a sum over the plain count. -/
theorem PolyZonotope.aux_sum_mergeKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) (f : Fin h → α) :
    (∑ j ∈ PolyZonotope.mergeKeep E, f j) = ∑ j, f (PolyZonotope.aux_mergeIdx E j) := by
  rw [← Finset.sum_coe_sort (PolyZonotope.mergeKeep E) f]
  exact (Equiv.sum_comp ((PolyZonotope.mergeKeep E).orderIsoOfFin rfl).toEquiv
    fun x => f x).symm

end


section
variable {α : Type} [AddCommGroup α]

/-- A column `merge` drops gathers nothing. -/
theorem PolyZonotope.aux_fiberSum_eq_zero_of_notMem_merge {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) {j : Fin h} (hj : j ∉ PolyZonotope.mergeKeep E) : -- --- CONCL ---
    PolyZonotope.fiberSum (PolyZonotope.rep E) G j = 0 := by -- --- PROOF ---
  rw [PolyZonotope.fiberSum]
  refine Finset.sum_eq_zero fun l hl => ?_
  exfalso
  -- `l` lands on `j`, so `j` carries `l`'s column and is its own representative
  have hrl : PolyZonotope.rep E l = j := (Finset.mem_filter.mp hl).2
  have hcol : PolyZonotope.col E j = PolyZonotope.col E l := by
    rw [← hrl, PolyZonotope.col_rep]
  exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (PolyZonotope.rep_congr E hcol).trans hrl⟩)

end


-- file-local: only `merge_point` below needs it
/-- The dependent generator sum, regrouped onto the columns that survive. -/
theorem PolyZonotope.aux_sum_merge (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) : -- --- CONCL ---
    (∑ i, PolyZonotope.monomial pZ.E a i • pZ.G i)
      = ∑ j : Fin pZ.merge.h,
          PolyZonotope.monomial pZ.merge.E a j • pZ.merge.G j := by -- --- PROOF ---
  rw [PolyZonotope.sum_monomial_merge pZ.E pZ.G a (PolyZonotope.rep pZ.E)
      (PolyZonotope.mergeKeep pZ.E) (PolyZonotope.col_rep pZ.E)
      fun j hj => PolyZonotope.aux_fiberSum_eq_zero_of_notMem_merge pZ.E pZ.G hj,
    PolyZonotope.aux_sum_mergeKeep]
  rfl


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.merge_point (pZ : PolyZonotope α) (a : Fin pZ.p → ℝ) :
    pZ.merge.point a = pZ.point a :=
  congrArg (fun s => pZ.c + s) (PolyZonotope.aux_sum_merge pZ a).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
