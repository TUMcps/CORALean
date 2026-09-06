import CORALean.ContSet.PolyZonotope.Real.Operations.Rep

/-!
# The columns `compact` keeps, over a floating-point scalar

Split out of `Compact.lean` (issue #62): read again by `keepIdx` in this
directory, by `Theorems/FiberEqZeroOfNotMem.lean` and
`Theorems/CompactGensOuter.lean`, and by `ConPolyZono`'s own compaction, all
outside this file.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Float

variable {p h : ℕ}

/-- The columns that survive: one per exponent column, the least index carrying
it. A column that is not its class's representative has an empty fibre, so
merging and dropping are one step here as they are over ℝ. -/
def PolyZonotope.repKeep (E : Fin p → Fin h → ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => Real.PolyZonotope.rep E j = j

end CORALean.Float
