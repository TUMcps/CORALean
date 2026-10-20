module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.ConPolyZono.Real.Operations.Plus
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor

@[expose] public section

/-!
# A capsule as a constrained polynomial zonotope, as CORA's `conPolyZono(C)`

`@capsule/conPolyZono.m`: the segment `conPolyZono(0, g, 1)`, one dependent generator of
exponent one, plus the ball `conPolyZono(ellipsoid(r² I))`, plus `c`. Here the segment is
`zonotope(c, g)` converted, which carries `c` itself, so the last sum is the first's center; the
ball is `Ellipsoid.ofFactor (r • 1) 0`. Both sums are exact, and so is the conversion for `0 ≤ r`.
CORA's branches for an empty radius or generator (`isempty(C.r)`, `isempty(C.g)`) concern empty
MATLAB fields, which a Lean capsule does not have; the last of them adds an undefined `s`.

## Inputs
* `C` – capsule

## Output
* constrained polynomial zonotope of the segment plus the ball
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `conPolyZono(C)`: the segment's plus the ball's. -/
noncomputable def Capsule.conPolyZono (C : Capsule n) : ConPolyZono (Vec ℝ n) :=
  -- `G`: the segment `zonotope(c, g)`, one generator of exponent one
  let G : ConPolyZono (Vec ℝ n) := (⟨1, C.c, fun _ => C.g⟩ : Zonotope (Vec ℝ n)).conPolyZono
  -- `S`: the ball `ellipsoid(r² I)`
  let S : ConPolyZono (Vec ℝ n) := (Ellipsoid.ofFactor (C.r • (1 : Mat ℝ n n)) 0).conPolyZono
  -- `G + S`
  G.plus S

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
