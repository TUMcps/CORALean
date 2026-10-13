module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Real.Operations.ReduceGirard

@[expose] public section

/-!
# `ConPolyZono.reduce`

CORA's `@conPolyZono/reduce` at Girard's rule: bring the generator count down to
a maximum order. `reduce` compacts first, so the count counts distinct
monomials, and compaction is also the only stage that moves `s`.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: compact, then rank. Compacting first is not an
optimization — a repeated exponent column is one monomial, and ranking before
merging would spend the budget twice on it. -/
noncomputable def ConPolyZono.reduce (cPZ : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    ConPolyZono (Vec ℝ n) :=
  cPZ.compact.reduceGirard o

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
