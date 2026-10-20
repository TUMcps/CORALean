module

public import CORALean.ContSet.ConZonotope.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `ConZonotope.reduce` bounds the generator count

`split_ifs`: above the order, `Zonotope.conZonotope` sets `h := Z.h`, so
`(cZ.zonotope.reduce o).conZonotope.h` is `(cZ.zonotope.reduce o).h` outright and
`Zonotope.reduce_order_le` closes it; at or below, `cZ` passes through and the
branch condition itself is the bound.

Unlike `ZonoBundle.reduce_order_le`, `0 < o` is needed: the bound is inherited
from Girard's rule, which reserves `n` of its budget for the box it adds. A
bundle's reduction adds nothing, so it needs no budget and no hypothesis.

## Inputs
* `cZ` – constrained zonotope
* `o` – target order

## Hypotheses
* `ho` – the order is positive

## Conclusion
* the reduced set has at most o * n generators
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ConZonotope.reduce_order_le (cZ : ConZonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (cZ.reduce o).h ≤ o * n := by
  unfold ConZonotope.reduce
  split_ifs with h
  · exact Zonotope.reduce_order_le _ ho
  · exact Nat.le_of_not_lt h

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
