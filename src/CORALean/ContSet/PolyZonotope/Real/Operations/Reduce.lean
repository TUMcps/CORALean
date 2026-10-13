import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirard

/-!
# `PolyZonotope.reduce`

CORA's `@polyZonotope/reduce`: bring the generator count down to a maximum
order, by the Girard rule of `ReduceGirard.lean` on both blocks.

One box covers both blocks because a monomial never leaves `[-1,1]`, so a
dropped dependent generator reaches no further than an independent coefficient.
CORA is tighter on an all-even column and ranks by `sum(G.^2)`, not Girard's.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: compact, then rank. Compacting first is not an
optimization — a repeated exponent column is one monomial, and ranking before
merging would spend the budget twice on it. -/
noncomputable def PolyZonotope.reduce (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  pZ.compact.reduceGirard o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
