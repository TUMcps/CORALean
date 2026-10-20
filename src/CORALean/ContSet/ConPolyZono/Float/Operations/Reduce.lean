module

public import CORALean.ContSet.ConPolyZono.Float.Operations.Compact
public import CORALean.ContSet.ConPolyZono.Float.Operations.ReduceGirard
public import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce

@[expose] public section

/-!
# `ConPolyZono.reduce`

The exact layer's `reduce`, rounded, and the one operation the float layer *runs* where the exact
layer only specifies: `reduceGirard` is noncomputable over ℝ because `Tuple.sort` needs a
`LinearOrder`, while `sortPerm` asks its comparator for nothing. A misranking costs precision,
never soundness (`reduceBy_outer`).

`reduceBy` copies the center, kept generators and constraint block exactly and rounds the diagonal
block up; the rounding of `reduce` is in `compact`, which it runs first.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `o` – target order

## Output
* enclosure of the set of reduced order
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   06-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: compact, then rank. A caller names an order and gets an
over-approximation of bounded size; which rule ranked it goes no further. -/
def ConPolyZono.reduce (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) (o : ℕ) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  cPZ.compact.reduceGirard o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
