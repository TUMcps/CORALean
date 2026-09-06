import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOuter

/-!
# `ConPolyZono.reduce` over-approximates the set

Compaction, which is an equality here as it is for `PolyZonotope`, followed by
Girard's rule. Neither choice shows in the proof: any ranking would discharge
the second step, and the first contributes nothing but a rewrite. What
compaction buys is the order bound, which is stated in `ReduceOrder`.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem ConPolyZono.reduce_outer (C : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    C.construct ⊆ (C.reduce o).construct :=
  (ConPolyZono.compact_exact C).subset.trans
    (ConPolyZono.reduceGirard_outer C.compact o)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
