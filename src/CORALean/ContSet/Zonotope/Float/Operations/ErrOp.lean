module

public import CORALean.ContSet.Zonotope.Float.Operations.AbsBoundError

@[expose] public section

/-!
# `Zonotope.errOp`

CORA's `priv_errOp` in the sup norm: the largest `absBoundError`, how far the
whole `construct` reaches from the origin in its farthest coordinate, rounded
up. CORA and [1] take `r(box(·))`, the Euclidean radius of the same box; `Vec`
carries the sup norm, and this is that norm's radius of the box, at most the
Euclidean one.

## References

* [1] M. Wetzlinger, N. Kochdumper and M. Althoff. "Adaptive parameter tuning
      for reachability analysis of linear systems". CDC, 2020, pp. 5145–5152.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The sup-norm radius of `Z`'s box about the origin, rounded up. -/
def Zonotope.errOp (Z : Zonotope (Vec 𝕋 n)) : 𝕋 :=
  maximumOver fun j => Z.absBoundError j

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
