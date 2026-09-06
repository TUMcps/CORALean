import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceByOuter

/-!
# Girard's reduction over-approximates

Two cases: below the order there is nothing to do, and above it the rule is a
pair of partitions like any other, so `reduceBy_outer` closes it. The metric
never appears, which is what leaves the ranking free to be a heuristic.
-/

-- Authors:       Tobias Ladner
-- Written:       05-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConPolyZono.reduceGirard_outer (C : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    C.construct ⊆ (C.reduceGirard o).construct := by -- --- PROOF ---
  unfold ConPolyZono.reduceGirard
  split_ifs with hlt
  · exact ConPolyZono.reduceBy_outer C _ _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
