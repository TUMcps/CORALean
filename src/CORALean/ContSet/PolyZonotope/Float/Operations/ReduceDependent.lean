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

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}

def PolyZonotope.reduceDependent (PZ : PolyZonotope 𝕋 n) (o : ℕ) : PolyZonotope 𝕋 n :=
  PZ.compact.reduceGirardDependent o

end CORALean.Float
