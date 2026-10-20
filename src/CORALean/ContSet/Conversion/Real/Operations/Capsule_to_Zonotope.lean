module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_Zonotope
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor
public import CORALean.ContSet.Zonotope.Real.Operations.Plus

@[expose] public section

/-!
# A capsule as a zonotope

CORA's `@capsule/zonotope.m`: the segment `zonotope(c, g)`, exactly, plus the zonotope of the
ball, `ellipsoid(r² I)` converted by the ellipsoid's own conversion, `Ellipsoid.zonotope`, unless
`r` is zero, where the conversion is exact. CORA converts the ball with `'outer:norm'` and
`order * n - 1` generators; here the ellipsoid's conversion is the existing one, the ellipsoid's
bounding box, so the ball's part is coarser than CORA's.

## Inputs
* `C` – capsule

## Output
* zonotope of the segment plus the ball
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A capsule as a zonotope, as CORA's `zonotope(capsule)`. -/
noncomputable def Capsule.zonotope (C : Capsule n) : Zonotope (Vec ℝ n) :=
  -- `Z = zonotope(C.c, C.g)`: the segment, one generator
  let Z : Zonotope (Vec ℝ n) := ⟨1, C.c, fun _ => C.g⟩
  -- `ellipsoid(C.r^2 * eye(n))`: the ball of radius `r`
  let E : Ellipsoid n := Ellipsoid.ofFactor (C.r • (1 : Mat ℝ n n)) 0
  -- `Z = Z + zonotope(E)`, unless `r` is zero
  if C.r = 0 then Z else Z.plus E.zonotope

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
