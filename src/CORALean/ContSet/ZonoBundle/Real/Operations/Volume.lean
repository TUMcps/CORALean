import CORALean.ContSet.ZonoBundle.Real.ZonoBundle
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# `ZonoBundle.volume`

CORA's `@zonoBundle/volume_`: `volume(polytope(zB))`, the volume of the bundle's polytope, which is
the Lebesgue measure of the set the bundle denotes. So the definition is that measure; the vertex
enumeration and convex hull CORA runs to compute it are not modelled.
-/

-- Authors:       Tobias Ladner
-- Written:       04-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The Lebesgue volume of the intersection. -/
noncomputable def ZonoBundle.volume (zB : ZonoBundle (Vec ℝ n)) : ENNReal :=
  MeasureTheory.volume zB.construct

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
