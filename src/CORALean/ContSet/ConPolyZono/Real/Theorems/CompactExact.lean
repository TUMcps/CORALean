import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactConsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactGensExact

/-!
# Compaction loses nothing

Three stages and three equalities of sets, none of them needing a hypothesis:
`compact` is bookkeeping, and an order bound is only worth stating once the
bookkeeping is done. The order matters — dropping factors is only sound once
both blocks have been merged onto the columns they keep.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- CORA's `compact`, and what an order bound would rest on: the set is
unchanged by any of the three stages. -/
theorem ConPolyZono.compact_exact (C : ConPolyZono α) :
    C.construct = C.compact.construct :=
  (ConPolyZono.compactGens_exact C).trans
    ((ConPolyZono.compactCons_exact C.compactGens).trans
      (ConPolyZono.compactFactors_exact C.compactGens.compactCons))

end CORALean.Real
