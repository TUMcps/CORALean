module

public import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
public import CORALean.ContSet.PolyZonotope.Real.Operations.FiberSum
public import CORALean.ContSet.PolyZonotope.Real.Operations.MergeKeep
public import CORALean.ContSet.PolyZonotope.Real.Operations.RepCongr

@[expose] public section

/-!
# A column `merge` drops gathers nothing

The hypothesis `sum_monomial_merge` asks for at the columns `merge` keeps: a
column that is not its own representative is nobody's representative, so its
fibre is empty and sums to zero. Empty, not merely zero-valued — which is why
this holds for every generator family and needs no cancellation.
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.fiberSum_eq_zero_of_notMem_merge {p h : ℕ} (E : Fin p → Fin h → ℕ)
    (G : Fin h → α) {j : Fin h} (hj : j ∉ PolyZonotope.mergeKeep E) :
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
