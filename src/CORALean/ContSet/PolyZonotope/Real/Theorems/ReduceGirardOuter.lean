import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceByOuter

/-!
# Girard's reduction over-approximates

Two cases: below the order there is nothing to do, and above it the rule is a
pair of partitions like any other, so `reduceBy_outer` closes it. The metric
never appears, which is what makes the bounded rule and the tighter one
interchangeable as far as soundness goes.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

theorem PolyZonotope.reduceGirard_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceGirard o).construct := by
  unfold PolyZonotope.reduceGirard
  split_ifs with hlt
  · exact PolyZonotope.reduceBy_outer PZ _ _
  · exact subset_rfl

end CORALean.Real
