import CORALean.ContSet.VPolytope.Float.VPolytope
import CORALean.ContSet.Interval.Float.Operations.Origin

/-!
# `VPolytope.emptySet`, over a floating-point scalar

No vertices, so there is no coefficient family summing to one: the nominal part
denotes `∅`, and so does its sum with any error box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float


variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def VPolytope.emptySet (𝕋 : Type) [FloatOps 𝕋] (n : ℕ) : VPolytope (Vec 𝕋 n) where
  k := 0
  V := Fin.elim0
  E := Interval.origin n

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
