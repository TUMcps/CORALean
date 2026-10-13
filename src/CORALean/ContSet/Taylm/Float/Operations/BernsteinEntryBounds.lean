import CORALean.ContSet.Taylm.Float.Operations.BernsteinStep
import CORALean.Global.Float.ListSum

/-!
# `Taylm.bernsteinEntryBounds`

`bernsteinEntry N e j`, the sum over `i ≤ e` of its terms, between two floats: the terms'
`bernsteinStep` brackets, the lower ends summed down and the upper ends summed up.
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

def Taylm.bernsteinEntryBounds (N e j : ℕ) : 𝕋 × 𝕋 :=
  (listSumDown ((List.range (e + 1)).map fun i => (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).1),
    listSumUp ((List.range (e + 1)).map fun i => (Taylm.bernsteinStep (𝕋 := 𝕋) N e j i).2))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
