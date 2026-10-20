module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Col
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# The canonical representative of an exponent column

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by every later step of `compact`, and by `ConPolyZono`'s own compaction
over `R`, all outside this file.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `i` – generator index

## Output
* the smallest index with the same exponent column
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The least index carrying the same exponent column. A canonical
representative is what makes the merge merge, and `Fin h`'s own order supplies
one, so only equality on the columns is needed and no order on them. -/
def PolyZonotope.rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) : Fin h :=
  (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
