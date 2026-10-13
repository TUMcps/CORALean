import CORALean.ContSet.Interval.Float.Operations.Center
import CORALean.ContSet.Interval.Float.Operations.CenterLo
import CORALean.ContSet.Interval.Float.Operations.Radius

/-!
# `Interval.enlarge` over floats

CORA's `@interval/enlarge`: `[c - f·r, c + f·r]` for the centre `c` and half-width `r`, scaled by a
nonnegative factor `f`. Each bound rounds outward: the lower one takes the centre rounded down
(`centerLo`) less the product `f · r` rounded up, with `r` rounded up (`radius`); the upper one the
centre rounded up (`center`) plus the same product.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.enlarge (I : Interval (Vec 𝕋 n)) (f : 𝕋) : Interval (Vec 𝕋 n) :=
  let r : Vec 𝕋 n := fun i => mulUp f (I.radius i)
  ⟨fun i => subDown (I.centerLo i) (r i), fun i => addUp (I.center i) (r i)⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
