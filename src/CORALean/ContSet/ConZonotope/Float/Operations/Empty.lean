import CORALean.ContSet.ConZonotope.Float.ConZonotope
import CORALean.ContSet.Interval.Float.Operations.Origin
import CORALean.ContSet.HPolytope.Float.Operations.EmptySet

/-!
# `ConZonotope.empty`, over a floating-point scalar

The centre `zero`, no generators, and `HPolytope.emptySet` as constraint, as over ℝ.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConZonotope.empty (n : ℕ) : ConZonotope 𝕋 (Vec 𝕋 n) where
  h := 0
  c := fun _ => zero
  G := Fin.elim0
  P := HPolytope.emptySet 𝕋 0
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
