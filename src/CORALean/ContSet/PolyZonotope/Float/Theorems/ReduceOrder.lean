module

public import CORALean.ContSet.PolyZonotope.Float.Operations.Reduce
public import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceGirardOrderLe

@[expose] public section

/-!
# `PolyZonotope.reduce` bounds the generator count

This is the guarantee the float layer needs most and the exact layer least: over
ℝ an unbounded generator count is a specification that grows, here it is memory
and time per step. It is false of `reduceDependent`, which is what that rule
trades for a tighter step.

At `o = 0` there is nothing to state: CORA's `K = max(0, N·order - N)` floors
the budget at nothing and the box of `n` is added regardless, so order zero
lands at order one in both tools.
-/

-- Authors:       Claude Opus 5
-- Written:       03-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem PolyZonotope.reduce_order_le (pZ : PolyZonotope (Vec 𝕋 n)) {o : ℕ} (ho : 0 < o) :
    (pZ.reduce o).h + (pZ.reduce o).q ≤ o * n :=
  PolyZonotope.reduceGirard_order_le pZ.compact ho

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
