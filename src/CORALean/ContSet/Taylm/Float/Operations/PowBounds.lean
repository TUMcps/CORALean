import CORALean.ContSet.Taylm.Float.Taylm
import CORALean.ContSet.Interval.Float.Operations.Power

/-!
# `Taylm.powBounds`, over a floating-point scalar

The range of `t ^ k` over `[l, u]`, by the float interval power `Interval.power` at one coordinate
(every end rounded outward).
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

def Taylm.powBounds (l u : 𝕋) (k : ℕ) : 𝕋 × 𝕋 :=
  let P : Interval (Vec 𝕋 1) := Interval.power ⟨fun _ => l, fun _ => u⟩ k
  (P.inf 0, P.sup 0)
end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
