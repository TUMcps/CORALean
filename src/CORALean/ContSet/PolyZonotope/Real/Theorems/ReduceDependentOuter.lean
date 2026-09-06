import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceDependent
import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardDependentOuter

/-!
# The tighter reduction over-approximates

Compaction, which is an equality, followed by the dependent-only rule. Sound on
the same line as the bounded rule, which is the point of `reduceBy_outer`
holding at every pair of partitions: what separates the two is the order bound
and nothing here.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- The tighter rule is sound on the same line as the bounded one, which is the
point of `reduceBy_outer` holding at every pair of partitions: what separates
the two is the order bound and nothing here. -/
theorem PolyZonotope.reduceDependent_outer (PZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PZ.construct ⊆ (PZ.reduceDependent o).construct :=
  (PolyZonotope.compact_exact PZ).subset.trans
    (PolyZonotope.reduceGirardDependent_outer PZ.compact o)

end CORALean.Real
