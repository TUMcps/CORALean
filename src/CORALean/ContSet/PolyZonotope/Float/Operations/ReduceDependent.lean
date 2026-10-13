import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirardDependent

/-!
# `PolyZonotope.reduceDependent`

Split out of `Reduce.lean` (issue #62): each `reduce`-family rule now earns its
own file, as CORA gives each a file too.

`reduce`'s shape at the dependent-only rule: compact, then rank.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.reduceDependent (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) : PolyZonotope (Vec 𝕋 n) :=
  pZ.compact.reduceGirardDependent o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
