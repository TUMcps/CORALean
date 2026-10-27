module

public import CORALean.ContSet.ZonoBundle.Real.Operations.Reduce
public import CORALean.ContSet.Zonotope.Real.Theorems.ReduceOrder

@[expose] public section

/-!
# `ZonoBundle.reduce` bounds each member's generator count

CORA's order bound read member by member: a bundle has no single order, each member of the reduced
bundle has at most `o * n` generators, as `Zonotope.reduce_order_le` states for one zonotope. The
member count is the operand's.

## Inputs
* `zB` – zonotope bundle
* `o` – maximum order
* `i` – member

## Hypotheses
* `ho` – order positive

## Conclusion
* the `i`-th member of the result has at most `o * n` generators
-/

-- Authors:       Claude Opus 5, Claude Sonnet 5.5
-- Written:       07-September-2026
-- Last update:   27-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem ZonoBundle.reduce_order_le (zB : ZonoBundle (Vec ℝ n)) {o : ℕ} (ho : 0 < o)
    (i : Fin zB.k) : ((zB.reduce o).Z i).h ≤ o * n :=
  Zonotope.reduce_order_le (zB.Z i) ho

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
