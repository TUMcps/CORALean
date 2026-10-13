module

public import CORALean.ContSet.HPolytope.Float.Operations.PairsToEq
public import CORALean.ContSet.HPolytope.Float.Operations.NormalizeRows

@[expose] public section

/-!
# `HPolytope.compactAtoAe` over a floating-point scalar

CORA's `compact_(P, 'AtoAe')`: the unit normalization of `compact_` (`normalizeRows`, which pays
its rounding on the right-hand sides over the box `dom`), then the inverted pairs turned into
equalities (`pairsToEq`, which is exact).
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

/-- The rows normalized, then each inverted pair of inequalities made an equality. -/
def HPolytope.compactAtoAe (p : ℕ) (P : HPolytope 𝕋 (Vec 𝕋 n)) (dom : Interval (Vec 𝕋 n)) :
    HPolytope 𝕋 (Vec 𝕋 n) :=
  (P.normalizeRows p dom).pairsToEq

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
