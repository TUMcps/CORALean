import CORALean.ContSet.PolyZonotope.Real.Operations.ColRep
import CORALean.ContSet.PolyZonotope.Real.Operations.Merge
import CORALean.ContSet.PolyZonotope.Real.Operations.RepCongr

/-!
# `merge` leaves no two columns equal

The true part of [1, Prop. 3.3]'s conclusion. A kept column is its own
representative, and `rep` reads its argument only through `col`, so two kept
columns that were equal would have the same representative and be the same
column.

This is *not* regularity: [1, Def. 2.4] also forbids an all-zero column, and
`merge` keeps one wherever the operand had one — [1, Alg. 2] never produces one,
which is why the gap does not bite there.

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


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem PolyZonotope.merge_col_injective (pZ : PolyZonotope α) :
    Function.Injective (PolyZonotope.col pZ.merge.E) := by -- --- PROOF ---
  intro j₁ j₂ hj
  -- every kept column is its own representative, by the filter `mergeKeep` is
  have hrep : ∀ j, PolyZonotope.rep pZ.E (PolyZonotope.mergeIdx pZ.E j)
      = PolyZonotope.mergeIdx pZ.E j :=
    fun j => (Finset.mem_filter.mp ((PolyZonotope.mergeKeep pZ.E).orderIsoOfFin rfl j).2).2
  have hc : PolyZonotope.col pZ.E (PolyZonotope.mergeIdx pZ.E j₁)
      = PolyZonotope.col pZ.E (PolyZonotope.mergeIdx pZ.E j₂) := hj
  have heq := PolyZonotope.rep_congr pZ.E hc
  rw [hrep, hrep] at heq
  exact ((PolyZonotope.mergeKeep pZ.E).orderIsoOfFin rfl).injective (Subtype.ext heq)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
