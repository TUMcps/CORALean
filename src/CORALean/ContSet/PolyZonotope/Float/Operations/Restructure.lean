module

public import CORALean.ContSet.PolyZonotope.Float.Operations.AbsorbRounding
public import CORALean.ContSet.PolyZonotope.Float.Operations.ReduceBy

@[expose] public section

/-!
# `PolyZonotope.restructure` over a floating-point scalar

CORA's `@polyZonotope/restructure` [1, Prop. 17] as the exact layer has it: the independent
block boxed away into one generator per coordinate, keeping every dependent generator and
dropping every independent one, and those boxes then made dependent. Only the boxing loses
anything, and `reduceBy` there rounds its radius up.

## References

* [1] N. Kochdumper and M. Althoff. "Sparse Polynomial Zonotopes: A Novel Set
      Representation for Reachability Analysis". IEEE Transactions on Automatic
      Control, 2021.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every independent generator boxed away into `n` diagonal ones, and those
made dependent: what comes back has an empty independent block. -/
def PolyZonotope.restructure (pZ : PolyZonotope (Vec 𝕋 n)) : PolyZonotope (Vec 𝕋 n) :=
  let reduced := pZ.reduceBy (Partition.split pZ.h 0)
    ((Partition.split 0 pZ.q).reindex (finCongr (Nat.zero_add pZ.q).symm))
  reduced.absorbRounding

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
