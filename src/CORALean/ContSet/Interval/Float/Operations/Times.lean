module

public import CORALean.ContSet.Interval.Float.Operations.MulHi
public import CORALean.ContSet.Interval.Float.Operations.MulLo

@[expose] public section

/-!
# `Interval.times`

The entrywise product, each coordinate the hull of the four corner products, rounded away from the
box: `mulLo` and `mulHi`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.times (I J : Interval (Vec 𝕋 n)) : Interval (Vec 𝕋 n) where
  inf := fun i => Interval.mulLo (I.inf i) (I.sup i) (J.inf i) (J.sup i)
  sup := fun i => Interval.mulHi (I.inf i) (I.sup i) (J.inf i) (J.sup i)


end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
