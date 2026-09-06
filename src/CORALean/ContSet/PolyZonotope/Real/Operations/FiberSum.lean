import CORALean.ContSet.PolyZonotope.Real.PolyZonotope

/-!
# The generators one representative gathers

Split out of `Compact.lean` (issue #62): shared with `compactKeep` and
`compactGens` in this directory, and read again by `ConPolyZono`'s own
compaction over `EC`, all outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- The generators a representative map gathers at `j`, added up: the one
generator their common column keeps. -/
def PolyZonotope.fiberSum {h : ℕ} (r : Fin h → Fin h) (G : Fin h → α) (j : Fin h) : α :=
  ∑ i ∈ Finset.univ.filter fun i => r i = j, G i

end CORALean.Real
