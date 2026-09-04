import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOuter

/-!
# `PolyZonotope.reduce` over-approximates the set

Compaction, which is an equality, followed by Girard's rule. Neither choice
shows in the proof: any ranking would discharge the second step, and the first
contributes nothing but a rewrite. What compaction buys is the order bound,
which is stated in `ReduceOrder`.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem PolyZonotope.reduce_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduce o).construct :=
  (PolyZonotope.compact_exact PZ).subset.trans
    (PolyZonotope.reduceGirard_outer PZ.compact o)

end CORALean.Real
