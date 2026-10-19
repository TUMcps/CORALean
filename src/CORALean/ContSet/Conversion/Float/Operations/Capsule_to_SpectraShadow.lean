module

public import CORALean.ContSet.Capsule.Float.Capsule
public import CORALean.ContSet.Conversion.Float.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.SpectraShadow.Float.Operations.Plus

@[expose] public section

/-!
# A capsule as a spectrahedral shadow, over a floating-point scalar

CORA's `spectraShadow(C)` as over ℝ: the ball `ellipsoid(r² I)`, its shape `r²` rounded up
(`Ellipsoid.ball`), as a shadow, plus the segment `zonotope(c, g)` as a shadow, the latter carrying
the capsule's error box. Both conversions store their entries without rounding; the sum pays its
center's rounding into the box.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `spectraShadow(C)`: the ball's shadow plus the segment's. -/
def Capsule.spectraShadow (C : Capsule 𝕋 n) : SpectraShadow 𝕋 (Vec 𝕋 n) :=
  -- `sphere = spectraShadow(r * ellipsoid(eye(n)))`
  let sphere := (Ellipsoid.ball n C.r).spectraShadow
  -- `segment = spectraShadow(zonotope(c, g))`, with the capsule's error box
  let segment := (⟨1, C.c, fun _ => C.g, C.I_error⟩ : Zonotope (Vec 𝕋 n)).spectraShadow
  -- `sphere + segment`
  sphere.plus segment

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
