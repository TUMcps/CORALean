module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Zonotope.Float.Operations.Plus

@[expose] public section

/-!
# A capsule as a zonotope, over a floating-point scalar

CORA's `@capsule/zonotope.m`, as over ℝ: the segment `zonotope(c, g)`, carrying the capsule's
error box, plus the zonotope of the ball, unless `r` is zero. The ball `ellipsoid(r² I)` is
enclosed by its bounding box `[-r, r]ⁿ`, which is what `Ellipsoid.zonotope` takes in the exact
layer; the float layer has no ellipsoid conversion, and the box of that ellipsoid is read off its
radius. `r` is zero where `le` says it is, both ways, so a `true` is exact and a `false` costs a
zero-width ball and nothing else.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   19-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- A capsule as a zonotope, as CORA's `zonotope(capsule)`, over a floating-point scalar. -/
def Capsule.zonotope (C : Capsule 𝕋 n) : Zonotope (Vec 𝕋 n) :=
  -- `Z = zonotope(C.c, C.g)`: the segment, one generator, the error box carried along
  let Z : Zonotope (Vec 𝕋 n) := ⟨1, C.c, fun _ => C.g, C.I_error⟩
  -- the box of `ellipsoid(C.r^2 * eye(n))`: the ball of radius `r`
  let B : Interval (Vec 𝕋 n) := ⟨fun _ => neg C.r, fun _ => C.r⟩
  -- `Z = Z + zonotope(B)`, unless `r` is zero
  if le C.r zero && le zero C.r then Z else Z.plus B.zonotope

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
