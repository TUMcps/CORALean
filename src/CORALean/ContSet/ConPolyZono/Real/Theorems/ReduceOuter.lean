module

public import CORALean.ContSet.ConPolyZono.Real.Operations.Reduce
public import CORALean.ContSet.ConPolyZono.Real.Theorems.CompactExact
public import CORALean.ContSet.ConPolyZono.Real.Theorems.ReduceGirardOuter

@[expose] public section

/-!
# `ConPolyZono.reduce` over-approximates the set

The operation and its guarantee are [1, Prop. 12].

Compaction, which is an equality here as it is for `PolyZonotope`, followed by
Girard's rule. Neither choice shows in the proof: any ranking would discharge
the second step, and the first contributes nothing but a rewrite. What
compaction buys is the order bound, which is stated in `ReduceOrder`.

## Inputs
* `cPZ` – constrained polynomial zonotope
* `o` – target order

## Hypotheses
* none

## Conclusion
* the set is contained in the result

## References

* [1] [N. Kochdumper and M. Althoff. "Constrained Polynomial Zonotopes". Acta Informatica,
      2023.](../../../../../../references/2023/kochdumper-constrained-polyzonotopes.md)
-/

-- Authors:       Claude Opus 5
-- Written:       05-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- Girard's is the rule `reduce` runs, and compaction is what makes the count
it bounds mean anything. Neither choice shows here: any ranking would discharge
this line, and compaction contributes an equality. -/
theorem ConPolyZono.reduce_outer (cPZ : ConPolyZono (Vec ℝ n)) (o : ℕ) :
    cPZ.construct ⊆ (cPZ.reduce o).construct :=
  (ConPolyZono.compact_exact cPZ).subset.trans
    (ConPolyZono.reduceGirard_outer cPZ.compact o)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
