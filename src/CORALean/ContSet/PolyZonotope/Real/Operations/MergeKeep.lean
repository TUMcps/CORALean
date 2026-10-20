module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

@[expose] public section

/-!
# The columns `merge` keeps

One index per distinct exponent column, the least carrying it. This is
`compactKeep` without the second half of a compaction: a column whose merged
generator came out zero stays, and so does the all-zero column, because
`merge` is asked to join equal columns and nothing else.

## Inputs
* `p` – number of factors
* `h` – number of generators
* `E` – exponent matrix

## Output
* set of the columns that represent themselves
-/

-- Authors:       Claude Opus 5
-- Written:       12-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The columns that survive a merge: those that are their own representative. -/
def PolyZonotope.mergeKeep {p h : ℕ} (E : Fin p → Fin h → ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => PolyZonotope.rep E j = j

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
