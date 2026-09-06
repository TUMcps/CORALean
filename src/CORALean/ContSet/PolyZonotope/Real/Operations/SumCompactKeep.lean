import CORALean.ContSet.PolyZonotope.Real.Operations.CompactIdx

/-!
# A sum over the kept columns is a sum over the plain count

Split out of `Compact.lean` (issue #62): used again by
`Theorems/CompactGensExact.lean`, outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

omit [Module ℝ α] in
theorem PolyZonotope.sum_compactKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) (G : Fin h → α)
    (f : Fin h → α) :
    ∑ j ∈ PolyZonotope.compactKeep E G, f j
      = ∑ j, f (PolyZonotope.compactIdx E G j) := by
  rw [← Finset.sum_coe_sort (PolyZonotope.compactKeep E G) f]
  exact (Equiv.sum_comp ((PolyZonotope.compactKeep E G).orderIsoOfFin rfl).toEquiv
    fun x => f x).symm

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
