import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
import CORALean.ContSet.ConPolyZono.Float.Operations.LongestFactor

/-!
# `ConPolyZono.splitLongestGen`, over a floating-point scalar

The two halves of `cPZ` along the factor of its longest generators, or the set twice where it has
no factor to split.
-/

-- Authors:       Tobias Ladner
-- Written:       03-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.splitLongestGen (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) :
    ConPolyZono 𝕋 (Vec 𝕋 n) × ConPolyZono 𝕋 (Vec 𝕋 n) :=
  match cPZ.longestFactor with
  | some k => cPZ.splitDepFactor k
  | none => (cPZ, cPZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
