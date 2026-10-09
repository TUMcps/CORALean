import CORALean.ContSet.SpectraShadow.Float.Operations.ConvHull

/-!
# `SpectraShadow.or`, over a floating-point scalar

CORA's `or(SpS, S)` of a spectrahedral shadow: `convHull_(SpS, S)`, the convex hull of the union.
-/

-- Authors:       Tobias Ladner
-- Written:       09-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --
namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def SpectraShadow.or (SpS S : SpectraShadow 𝕋 n) : SpectraShadow 𝕋 n :=
  SpS.convHull_ S

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
