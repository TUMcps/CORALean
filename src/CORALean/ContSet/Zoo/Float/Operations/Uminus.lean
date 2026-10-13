import CORALean.ContSet.Zoo.Float.Zoo
import CORALean.ContSet.Taylm.Float.Operations.Uminus
import CORALean.ContSet.Interval.Float.Operations.Uminus

/-!
# `Zoo.uminus`, over a floating-point scalar

Every member negated: `Taylm.uminus` and `Interval.uminus`, both exact in floats.
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

def Zoo.uminus (Z : Zoo 𝕋 n) : Zoo 𝕋 n := ⟨Z.taylm.map Taylm.uminus, Z.ivl.map Interval.uminus⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
