import CORALean.ContSet.Zonotope.Float.Theorems.ContainsPointSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Specification.Instances

/-!
# A zonotope certified inside another, run

At `Dyadic 53`. `Contains.contains` on zonotopes, by Sadraddini and Tedrake's coefficients
with the rounding absorbed. `[-2, 2]²` is certified to contain the unit square shifted by
`(1/2, 0)` and a diagonal segment through the origin, and not the unit square centered at
`(3, 0)`. It is also not certified to contain itself: a set touching the boundary leaves no
margin for the rounding, so that `false` decides nothing.
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.ZonotopeContainsFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[-2, 2]²`, a unit square shifted by `(1/2, 0)`, one centered at `(3, 0)`, a diagonal
segment. -/
def big : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 2 0, d 0 0], ![d 0 0, d 2 0]], box0⟩
def inside : Zonotope (Vec D 2) :=
    ⟨2, ![d 1 (-1), d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def outside : Zonotope (Vec D 2) := ⟨2, ![d 3 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def diagonal : Zonotope (Vec D 2) := ⟨1, ![d 0 0, d 0 0], ![![d 1 0, d 1 0]], box0⟩

#eval Contains.contains big inside     -- true
#eval Contains.contains big outside    -- false
#eval Contains.contains big diagonal   -- true
#eval Contains.contains big big        -- false: touching the boundary is not certified

end CORALean.Examples.ZonotopeContainsFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
