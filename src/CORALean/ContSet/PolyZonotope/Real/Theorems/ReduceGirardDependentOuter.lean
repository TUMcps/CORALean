import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirardDependent
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByOuter

/-!
# The dependent-only reduction over-approximates

Word for word Girard's proof at a different pair of partitions, which is the
point of `reduceBy_outer` holding at every pair. What separates this rule from
the bounded one is the order bound and nothing here: it never cuts the
independent block, so no order bound is available for it.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.reduceGirardDependent_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirardDependent o).construct := by -- --- PROOF ---
  unfold PolyZonotope.reduceGirardDependent
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
