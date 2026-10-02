import CORALean.ContSet.Interval.Float.Operations.ProdUp
import CORALean.ContSet.Interval.Float.Operations.WidthUp

/-!
# `Interval.volume` over floats

CORA's `volume_`, the product of the widths, as an upper bound: each width rounded up and clipped at
zero (a crossed coordinate denotes `∅` and counts as `0`, as over ℝ), the product rounded up.
-/

-- Authors:       Tobias Ladner
-- Written:       02-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Interval.volume (I : Interval (Vec 𝕋 n)) : 𝕋 := prodUp fun i => I.widthUp i

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
