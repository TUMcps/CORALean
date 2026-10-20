module

public import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

@[expose] public section

/-!
# The generators one representative gathers

Split out of `Compact.lean` (issue #62): shared with `compactKeep` and
`compactGens` in this directory, and read again by `ConPolyZono`'s own
compaction over `R`, all outside this file.

## Inputs
* `h` – number of generators
* `r` – representative map
* `G` – generators
* `j` – representative index

## Output
* sum of the generators represented by that index
-/

-- Authors:       Claude Opus 5
-- Written:       06-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The generators a representative map gathers at `j`, added up: the one
generator their common column keeps. -/
def PolyZonotope.fiberSum {h : ℕ} (r : Fin h → Fin h) (G : Fin h → α) (j : Fin h) : α :=
  ∑ i ∈ Finset.univ.filter fun i => r i = j, G i

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
