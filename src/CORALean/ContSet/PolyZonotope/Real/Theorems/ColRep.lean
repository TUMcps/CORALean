module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# A representative's column is the column it represents

Split out of `Compact.lean` (issue #62): used again by `Theorems/RepIdem.lean`
and by `Theorems/CompactGensExact.lean`, both outside this file.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix
* `i` – generator index

## Hypotheses
* none

## Conclusion
* the representative has the same exponent column
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.col_rep {p h : ℕ} (E : Fin p → Fin h → ℕ) (i : Fin h) :
    PolyZonotope.col E (PolyZonotope.rep E i) = PolyZonotope.col E i := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter fun i' => PolyZonotope.col E i' = PolyZonotope.col E i)
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  exact (Finset.mem_filter.mp hmem).2

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
