import CORALean.ContSet.PolyZonotope.Real.Operations.MergeIdx

/-!
# A sum over the kept columns is a sum over the plain count

`sum_compactKeep` at the columns `merge` keeps: the same reindexing, over a
different `Finset`, and needed wherever a sum written over the result's `Fin h`
has to meet one written over the operand's surviving columns.
-/

-- Authors:       Tobias Ladner
-- Written:       12-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.sum_mergeKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) (f : Fin h → α) :
    (∑ j ∈ PolyZonotope.mergeKeep E, f j) = ∑ j, f (PolyZonotope.mergeIdx E j) := by
  rw [← Finset.sum_coe_sort (PolyZonotope.mergeKeep E) f]
  exact (Equiv.sum_comp ((PolyZonotope.mergeKeep E).orderIsoOfFin rfl).toEquiv
    fun x => f x).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
