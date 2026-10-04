import CORALean.ContSet.Zoo.Float.Zoo
import CORALean.ContSet.Taylm.Float.Operations.Plus
import CORALean.ContSet.Interval.Float.Operations.Plus

/-!
# `Zoo.plus`, over a floating-point scalar

Members combined as in the exact layer: the float Taylor models by `Taylm.plus`, the intervals by
`Interval.plus`, kept where both zoos have them.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Zoo.plus (Z₁ Z₂ : Zoo 𝕋 n) : Zoo 𝕋 n :=
  ⟨Option.map₂ Taylm.plus Z₁.taylm Z₂.taylm, Option.map₂ Interval.plus Z₁.ivl Z₂.ivl⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
