import CORALean.ContSet.Interval.Float.Interval
import CORALean.Global.Float.FloatOps

/-!
# The derivative enclosure of ReLU
CORA's derivative of ReLU is `1` for `x > 0` and `0` otherwise. On a box it is `1` only when the
lower bound is certified positive, `0` only when the upper bound is certified nonpositive, and
`[0, 1]` across the kink.
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

def reluDerEnclosure (I : Interval 𝕋) : Interval 𝕋 :=
  ⟨if ltStrict zero I.inf then one else zero, if le I.sup zero then zero else one⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
