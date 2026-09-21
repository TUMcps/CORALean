import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOrderLe

/-!
# `PolyZonotope.reduce` bounds the generator count

The order bound half of [1, Prop. 16] — `ReduceOuter.lean` carries the other
half, the enclosure.

The other half of what `reduce` is for, and the half no `_outer` theorem sees:
an enclosure the size of the state space is sound too, and so is one whose
representation grows every step. `reduce o` returns at most `o·n` generators,
dependent and independent together, whatever it is called on.

Compacting first only lowers the count `reduceGirard_order_le` then bounds, so
the bound reads off unchanged.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       03-September-2026
-- Last update:   21-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Compacting first only lowers the count it then bounds, so the bound reads
off `reduceGirard` unchanged. -/
theorem PolyZonotope.reduce_order_le (pZ : PolyZonotope (Vec ℝ n)) {o : ℕ} (ho : 0 < o) :
    (pZ.reduce o).h + (pZ.reduce o).q ≤ o * n :=
  PolyZonotope.reduceGirard_order_le pZ.compact ho

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
