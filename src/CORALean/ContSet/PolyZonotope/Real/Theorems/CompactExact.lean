import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactFactorsExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactGensExact

/-!
# Compaction loses nothing

The two stages composed. Every step is an equality of sets and needs no
hypothesis, which is the point: `compact` is bookkeeping, and an order bound is
only worth stating once the bookkeeping is done.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

/-- CORA's `compact`, and what an order bound rests on: the set is unchanged. -/
theorem PolyZonotope.compact_exact (PZ : PolyZonotope α) :
    PZ.construct = PZ.compact.construct :=
  (PolyZonotope.compactGens_exact PZ).trans
    (PolyZonotope.compactFactors_exact PZ.compactGens)

end CORALean.Real
