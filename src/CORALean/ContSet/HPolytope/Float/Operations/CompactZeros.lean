import CORALean.ContSet.HPolytope.Float.Operations.DropZeros
import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows

/-!
# `HPolytope.compactZeros` over a floating-point scalar

CORA's `compact_(P, 'zeros')`: the unit normalization of `compact_` (`normalizeRows`, which pays
its rounding on the right-hand sides over the box `dom`), then the zero-row step (`dropZeros`,
which is exact).
-/

-- Authors:       Tobias Ladner
-- Written:       12-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows normalized, then the zero rows dropped or the empty set returned. -/
def HPolytope.compactZeros (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  (P.normalizeRows p dom).dropZeros

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
