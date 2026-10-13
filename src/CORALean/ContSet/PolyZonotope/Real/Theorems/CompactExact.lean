module

public import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactFactorsExact
public import CORALean.ContSet.PolyZonotope.Real.Theorems.CompactGensExact

@[expose] public section

/-!
# Compaction loses nothing

The result is [1, Prop. 2].

The two stages composed. Every step is an equality of sets and needs no
hypothesis, which is the point: `compact` is bookkeeping, and an order bound is
only worth stating once the bookkeeping is done.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   04-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

/-- CORA's `compact`, and what an order bound rests on: the set is unchanged. -/
theorem PolyZonotope.compact_exact (pZ : PolyZonotope α) :
    pZ.construct = pZ.compact.construct :=
  (PolyZonotope.compactGens_exact pZ).trans
    (PolyZonotope.compactFactors_exact pZ.compactGens)

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
