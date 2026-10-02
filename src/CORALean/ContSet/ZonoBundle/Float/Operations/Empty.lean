import CORALean.ContSet.ZonoBundle.Float.ZonoBundle
import CORALean.ContSet.Zonotope.Float.Operations.Origin

/-!
# `ZonoBundle.empty`, over a floating-point scalar

The bundle of the points `0` and `e₀`, for `0 < n`, as over ℝ: two point zonotopes
whose intersection is empty. The second centre is `one` in the first coordinate
and `zero` elsewhere.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ZonoBundle.empty (n : ℕ) (hn : 0 < n) : ZonoBundle 𝕋 n :=
  ⟨2, ![Zonotope.origin n, Zonotope.point fun i => if i = ⟨0, hn⟩ then one else zero]⟩

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
