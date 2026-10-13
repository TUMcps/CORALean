module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceGirardDependent

@[expose] public section

/-!
# `PolyZonotope.reduceDependent`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

`reduce`'s shape at the dependent-only rule: compact, then rank.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

noncomputable def PolyZonotope.reduceDependent (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    PolyZonotope (Vec ℝ n) :=
  pZ.compact.reduceGirardDependent o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
