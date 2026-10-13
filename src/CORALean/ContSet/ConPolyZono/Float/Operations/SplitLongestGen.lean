module

public import CORALean.ContSet.ConPolyZono.Float.Operations.SplitDepFactor
public import CORALean.ContSet.ConPolyZono.Float.Operations.LongestFactor

@[expose] public section

/-!
# `ConPolyZono.splitLongestGen`, over a floating-point scalar

The two halves of `cPZ` along the factor of its longest generators, or the set twice where it has
no factor to split.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


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
