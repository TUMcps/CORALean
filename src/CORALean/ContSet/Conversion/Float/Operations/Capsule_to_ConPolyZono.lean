module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.ConPolyZono.Float.Operations.Plus
public import CORALean.ContSet.Conversion.Float.Operations.Basic
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_ConPolyZono
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic

@[expose] public section

/-!
# A capsule as a constrained polynomial zonotope, over a floating-point scalar

CORA's `conPolyZono(C)` as over ℝ: the segment `zonotope(c, g)` converted, carrying the capsule's
error box, plus the ball `ellipsoid(r² I)` converted, its shape `r²` rounded up
(`Ellipsoid.ball`, which holds the real ball by `Ellipsoid.ball_contains`). The ellipsoid's
conversion takes a certified factor of the shape from above (`Ellipsoid.conPolyZono`), and the
sum pays its rounding into the box.

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

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `conPolyZono(C)`: the segment's plus the ball's. -/
def Capsule.conPolyZono (C : Capsule 𝕋 n) : ConPolyZono 𝕋 (Vec 𝕋 n) :=
  -- `G`: the segment `zonotope(c, g)`, with the capsule's error box
  let G := (⟨1, C.c, fun _ => C.g, C.I_error⟩ : Zonotope (Vec 𝕋 n)).conPolyZono
  -- `S`: the ball `ellipsoid(r² I)`
  let S := (Ellipsoid.ball n C.r).conPolyZono
  -- `G + S`
  G.plus S

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
