module

public import CORALean.ContSet.Zonotope.Float.Operations.ReduceGirard

@[expose] public section

/-!
# `Zonotope.reduce`

The exact layer's `reduce`, rounded: `reduceBy` keeps the generators a partition
names and boxes the rest, a metric ranks them, and a split turns the ranking
into the partition. Girard's rule is the one used here.

## Inputs
* `Z` – zonotope
* `o` – target order

## Output
* zonotope of order at most `o` enclosing the input
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `reduce`: to a maximum order, by whichever rule the representation
sees fit. Girard's is the one here, as over ℝ, and which it is goes no further —
a caller names an order and gets an over-approximation. -/
def Zonotope.reduce (Z : Zonotope (Vec 𝕋 n)) (o : ℕ) : Zonotope (Vec 𝕋 n) :=
  Z.reduceGirard o

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
