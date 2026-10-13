module

public import CORALean.ContSet.PolyZonotope.Real.Operations.Dependent
public import CORALean.ContSet.PolyZonotope.Real.Operations.ReduceBy

@[expose] public section

/-!
# `PolyZonotope.restructure`

CORA's `@polyZonotope/restructure` [1, Prop. 17]: the representation with no
independent generators left. The independent block is boxed into one generator
per coordinate and those are then made dependent, under the partitions that keep
every dependent generator and drop every independent one — the paper's
`reduce(⟨0, GI⟩_Z, 1)`.

Only the boxing loses anything. Freeing an independent coefficient into a fresh
factor is exact, so this is `reduceBy` followed by `dependent` rather than a
construction of its own, and the enclosure is `reduceBy`'s and no wider. CORA
pairs the same conversion with four further reductions.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every independent generator boxed away into `n` diagonal ones, and those
made dependent: what comes back has an empty independent block. -/
def PolyZonotope.restructure (pZ : PolyZonotope (Vec ℝ n)) : PolyZonotope (Vec ℝ n) :=
  (pZ.reduceBy (Partition.split pZ.h 0)
    ((Partition.split 0 pZ.q).reindex (finCongr (Nat.zero_add pZ.q).symm))).dependent

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
