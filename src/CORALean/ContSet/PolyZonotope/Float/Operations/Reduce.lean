import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirard

/-!
# `PolyZonotope.reduce`

The exact layer's `reduce`, rounded — and the one operation the float layer
*runs* where the exact layer only specifies: `reduceGirard` is noncomputable
over ℝ because `Tuple.sort` needs a `LinearOrder`, while `sortPerm` asks its
comparator for nothing. It can afford to, `reduceBy_outer` holding at every pair
of partitions, so a misranking costs precision and never soundness.

`compact`, which `reduce` runs first, is the one place this operation charges
the box: merging two columns adds their entries, and running it first is what
makes the order bound count distinct monomials rather than stored columns.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation of bounded size. -/
def PolyZonotope.reduce (pZ : PolyZonotope (Vec 𝕋 n)) (o : ℕ) : PolyZonotope (Vec 𝕋 n) :=
  pZ.compact.reduceGirard o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
