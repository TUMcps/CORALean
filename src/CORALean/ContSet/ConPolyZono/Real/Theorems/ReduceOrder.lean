import CORALean.ContSet.ConPolyZono.Real.Operations.Compact
import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOrderLe

/-!
# `ConPolyZono.reduce` bounds the generator count

The order bound half of [1, Prop. 12] — `ReduceOuter.lean` carries the other
half, the enclosure.

The other half of what `reduce` is for, and the half no `_outer` theorem sees:
an enclosure the size of the state space is sound too, and so is one whose
representation grows every step. `reduce o` returns at most `o·n` generators,
dependent and independent together, whatever it is called on.

Compacting first only lowers the count `reduceGirard_order_le` then bounds, so
the bound reads off unchanged.

## References

* [1] N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta
      Informatica, 2023.
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   21-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem ConPolyZono.reduce_order_le (cPZ : ConPolyZono (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (cPZ.reduce o).h + (cPZ.reduce o).q ≤ o * n :=
  ConPolyZono.reduceGirard_order_le cPZ.compact ho

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
