import CORALean.ContSet.PolyZonotope.Real.Operations.Col

/-!
# The canonical representative of an exponent column

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by every later step of `compact`, and by `ConPolyZono`'s own compaction
over `EC`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

/-- The least index carrying the same exponent column. A canonical
representative is what makes the merge merge, and `Fin h`'s own order supplies
one, so only equality on the columns is needed and no order on them. -/
def PolyZonotope.rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin h :=
  (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

end CORALean.Real
