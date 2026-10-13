import CORALean.ContSet.HPolytope.Float.Operations.DropAligned
import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows

/-!
# `HPolytope.compactAlignedIneq` over a floating-point scalar

The inequality half of CORA's `compact_(P, 'aligned')`: the unit normalization of `compact_`
(`normalizeRows`, which pays its rounding on the right-hand sides over the box `dom`), then the
merging of rows with equal normals (`dropAligned`, which is exact).
-/

-- Authors:       Claude Opus 5.5
-- Written:       12-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The rows normalized, then the dominated rows with an equal normal dropped. -/
def HPolytope.compactAlignedIneq (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  (P.normalizeRows p dom).dropAligned

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
