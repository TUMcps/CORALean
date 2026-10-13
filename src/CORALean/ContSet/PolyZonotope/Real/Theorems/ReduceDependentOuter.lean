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

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- The tighter rule is sound on the same line as the bounded one, which is the
point of `reduceBy_outer` holding at every pair of partitions: what separates
the two is the order bound and nothing here. -/
theorem PolyZonotope.reduceDependent_outer (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduceDependent o).construct :=
  (PolyZonotope.compact_exact pZ).subset.trans
    (PolyZonotope.reduceGirardDependent_outer pZ.compact o)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
