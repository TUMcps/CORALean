import CORALean.ContSet.VPolytope.Float.Operations.IsFullDim
import CORALean.ContSet.VPolytope.Float.Theorems.IsFullDimSound
import CORALean.ContSet.Zonotope.Float.Theorems.IsFullDimSound
import CORALean.Global.Float.Instances.Dyadic.Instances
import CORALean.Specification.Instances

/-!
# Full-dimensionality of generators and vertices, certified by a rank test

At `Dyadic 53`. `Zonotope.isFullDim` accepts a full-rank generator matrix — square, wide, and
so ill-conditioned (second generator `(1, 2⁻³⁰)`) that a naive rank test is on the edge —
and refuses a rank-deficient one, two parallel generators. `VPolytope.isFullDim` is the
same question of a vertex list: a triangle spans the plane, three collinear points a line.

Each `true` is a guarantee (`Zonotope.isFullDim_sound`, `VPolytope.isFullDim_sound`); a
`false` decides nothing.

## Inputs
* none

## Output
* triangle with the checked vertices
-/

-- Authors:       Claude Opus 5.5, Claude Sonnet 5.5
-- Written:       04-October-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Examples.FullDimRankFloat

open CORALean CORALean.Float FloatOps

abbrev D := Dyadic 53

/-- `m · 2 ^ e`. -/
def d (m e : ℤ) : D := ⟨m, e⟩

/-- No rounding error. -/
def box0 : Interval (Vec D 2) := ⟨fun _ => d 0 0, fun _ => d 0 0⟩

/-- Zonotopes centered at the origin: invertible, rank one, wide, and nearly singular. -/
def zInv : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 1 0, d 1 0]], box0⟩
def zRank1 : Zonotope (Vec D 2) := ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 1 0], ![d 1 0, d 1 0]], box0⟩
def zWide : Zonotope (Vec D 2) :=
  ⟨3, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 0 0, d 1 0], ![d 1 0, d 1 0]], box0⟩
def zNear : Zonotope (Vec D 2) :=
    ⟨2, ![d 0 0, d 0 0], ![![d 1 0, d 0 0], ![d 1 0, d 1 (-30)]], box0⟩

#eval zInv.isFullDim     -- true
#eval zRank1.isFullDim   -- false, the generators span a line
#eval zWide.isFullDim    -- true
#eval zNear.isFullDim    -- true


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A triangle and three collinear points, as vertices. -/
def triangle : VPolytope (Vec D 2) :=
    ⟨3, ![![d 0 0, d 0 0], ![d 1 0, d 0 0], ![d 0 0, d 1 0]], box0⟩
def segment : VPolytope (Vec D 2) := ⟨3, ![![d 0 0, d 0 0], ![d 1 0, d 1 0], ![d 2 0, d 2 0]], box0⟩

#eval triangle.isFullDim   -- true
#eval segment.isFullDim    -- false, the points lie on a line

end CORALean.Examples.FullDimRankFloat


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
