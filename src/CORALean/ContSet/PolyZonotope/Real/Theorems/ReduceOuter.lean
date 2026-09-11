import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactExact
import CORALean.ContSet.PolyZonotope.Real.Theorems.ReduceGirardOuter

/-!
# `PolyZonotope.reduce` over-approximates the set

The operation and its guarantee are [1, Prop. 16].

Compaction, which is an equality, followed by Girard's rule. Neither choice
shows in the proof: any ranking would discharge the second step, and the first
contributes nothing but a rewrite. What compaction buys is the order bound,
which is stated in `ReduceOrder`.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem PolyZonotope.reduce_outer (pZ : PolyZonotope (Vec ℝ n)) (o : ℕ) :
    pZ.construct ⊆ (pZ.reduce o).construct :=
  (PolyZonotope.compact_exact pZ).subset.trans
    (PolyZonotope.reduceGirard_outer pZ.compact o)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
