import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# A representative's column is the column it represents

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by `Theorems/CompactGensExact.lean`, both outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

theorem PolyZonotope.col_rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) :
    PolyZonotope.col E (PolyZonotope.rep E i) = PolyZonotope.col E i := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i)
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  exact (Finset.mem_filter.mp hmem).2

end CORALean.Real
