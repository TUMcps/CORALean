import CORALean.ContSet.PolyZonotope.Float.Operations.SplitDepFactor
import CORALean.ContSet.PolyZonotope.Float.Operations.LongestFactor

/-!
# `PolyZonotope.splitLongestGen`, over a floating-point scalar

The two halves of `pZ` along the factor of its longest generator, or the set twice where it has no
dependent generator.
-/

-- Authors:       Claude Opus 5.5
-- Written:       03-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.splitLongestGen (pZ : PolyZonotope (Vec 𝕋 n)) :
    PolyZonotope (Vec 𝕋 n) × PolyZonotope (Vec 𝕋 n) :=
  match pZ.longestFactor with
  | some k => pZ.splitDepFactor k
  | none => (pZ, pZ)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
