module

public import CORALean.ContSet.Interval.Float.Interval
public import CORALean.Global.Float.FloatOps

@[expose] public section

/-!
# The value enclosure of ReLU
`[max 0 l, max 0 u]` of the box `[l, u]`: the activation `max 0` is monotone.
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

def reluEnclosure (I : Interval 𝕋) : Interval 𝕋 := ⟨maximum zero I.inf, maximum zero I.sup⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
