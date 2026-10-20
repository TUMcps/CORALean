module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Compact
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceGirard

@[expose] public section

/-!
# `PolyZonotope.reduce`

The exact layer's `reduce`, rounded, and the one operation the float layer
*runs* where the exact layer only specifies: `reduceGirard` is noncomputable
over ℝ because `Tuple.sort` needs a `LinearOrder`, while `sortPerm` asks its
comparator for nothing. `reduceBy_outer` holds at every pair of partitions, so a
misranking costs precision and never soundness.

`compact`, which `reduce` runs first, is the one place this operation charges
the box: it makes the order bound count distinct monomials, not stored columns.

## Inputs
* `pZ` – polynomial zonotope
* `o` – target order

## Output
* compacted polynomial zonotope of reduced order
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


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
