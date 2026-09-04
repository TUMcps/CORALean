import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOrderLe

/-!
# `PolyZonotope.reduce` bounds the generator count

The other half of what `reduce` is for, and the half no `_outer` theorem sees:
an enclosure the size of the state space is sound too, and so is one whose
representation grows every step. `reduce o` returns at most `o·n` generators,
dependent and independent together, whatever it is called on.

Compacting first only lowers the count `reduceGirard_order_le` then bounds, so
the bound reads off unchanged.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   04-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {n : ℕ}

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem PolyZonotope.reduce_order_le (PZ : PolyZonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (PZ.reduce o).h + (PZ.reduce o).q ≤ o * n :=
  PolyZonotope.reduceGirard_order_le PZ.compact ho

end CORALean.Real
