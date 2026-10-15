module

public import CORALean.ContSet.Ellipsoid.Float.Ellipsoid
public import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.minkDiffPoint`, over a floating-point scalar

CORA's `@ellipsoid/minkDiff` with a vector subtrahend, `ellipsoid(E.Q, E.c - s)`: the center
moves, the generators stay. The new center is rounded down, and what that leaves is paid into
the error box (`centerResidual`, the same box `plus` pays).
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.minkDiffPoint (E : Ellipsoid 𝕋 n) (s : Vec 𝕋 n) : Ellipsoid 𝕋 n :=
  -- `neg` is exact, so the difference is the sum with `-s`
  let negS : Vec 𝕋 n := (-s)
  { k := E.k
    c := fun i => addDown (E.c i) (negS i)
    G := E.G
    I_error := E.I_error.plus (Ellipsoid.centerResidual E.c negS) }

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
