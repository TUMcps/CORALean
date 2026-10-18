module

public import CORALean.ContSet.Taylm.Float.Taylm
public import CORALean.Global.Float.ListSum
public import CORALean.ContSet.Interval.Float.Operations.MulLo
public import CORALean.ContSet.Interval.Float.Operations.MulHi

@[expose] public section

/-!
# `Taylm.smul`

Scaling by any real in `[alo, ahi]`, which a number is at `alo = ahi` and an enclosed
coefficient such as `exp c / k!` is in general. Each coefficient product is enclosed by its
corner products; the upper one is stored and the width goes to the error box, a monomial
being at most one in magnitude on the box. The remainder and the box are each scaled by the
interval, rounded outward.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   18-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Taylm.smul (alo ahi : 𝕋) (T : Taylm 𝕋 n) : Taylm 𝕋 n :=
  -- what storing the upper corner costs, summed over the terms
  let err := listSumUp (T.terms.map fun b =>
    subUp (Interval.mulHi alo ahi b.1 b.1) (Interval.mulLo alo ahi b.1 b.1))
  ⟨T.terms.map fun b => (Interval.mulHi alo ahi b.1 b.1, b.2),
    ⟨Interval.mulLo alo ahi T.rem.inf T.rem.sup, Interval.mulHi alo ahi T.rem.inf T.rem.sup⟩,
    ⟨subDown (Interval.mulLo alo ahi T.I_error.inf T.I_error.sup) err,
      addUp (Interval.mulHi alo ahi T.I_error.inf T.I_error.sup) err⟩, T.maxOrder⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
