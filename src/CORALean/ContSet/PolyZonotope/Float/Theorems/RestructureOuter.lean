import CORALean.ContSet.PolyZonotope.Float.Operations.Restructure
import CORALean.ContSet.PolyZonotope.Float.Theorems.DependentOuter
import CORALean.ContSet.PolyZonotope.Float.Theorems.ReduceByOuter

/-!
# `PolyZonotope.restructure` encloses the set, in float too

Boxing the independent block is the step that widens; making the box dependent only adds
a zero to the error box.
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem PolyZonotope.restructure_outer (pZ : PolyZonotope (Vec 𝕋 n)) :
    pZ.construct ⊆ pZ.restructure.construct :=
  (PolyZonotope.reduceBy_outer pZ _ _).trans (PolyZonotope.dependent_outer _)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
