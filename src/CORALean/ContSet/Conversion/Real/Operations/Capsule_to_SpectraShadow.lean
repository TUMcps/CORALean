module

public import CORALean.ContSet.Capsule.Real.Capsule
public import CORALean.ContSet.Conversion.Real.Operations.Ellipsoid_to_SpectraShadow
public import CORALean.ContSet.Conversion.Real.Operations.Zonotope_to_SpectraShadow
public import CORALean.ContSet.Ellipsoid.Real.Operations.OfFactor
public import CORALean.ContSet.SpectraShadow.Real.Operations.Plus

@[expose] public section

/-!
# A capsule as a spectrahedral shadow, as CORA's `spectraShadow(C)`

`@capsule/spectraShadow.m`: the ball `r · ellipsoid(I)` as a shadow, plus the segment
`zonotope(c, g)` as a shadow. The ball is `Ellipsoid.ofFactor (r • 1) 0`, CORA's `r · ellipsoid(I)`
being the ellipsoid of shape `r² I`. Both conversions and the sum are exact, so the shadow is the
capsule for `0 ≤ r`. CORA also sets the shadow's cached properties (bounded, empty,
full-dimensional, center), which a Lean shadow does not carry.
-/

-- Authors:       Claude Opus 5.5
-- Written:       19-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `spectraShadow(C)`: the ball's shadow plus the segment's. -/
noncomputable def Capsule.spectraShadow (C : Capsule n) : SpectraShadow (Vec ℝ n) :=
  -- `sphere = spectraShadow(r * ellipsoid(eye(n)))`
  let sphere := (Ellipsoid.ofFactor (C.r • (1 : Mat ℝ n n)) 0).spectraShadow
  -- `segment = spectraShadow(zonotope(c, g))`
  let segment := (⟨1, C.c, fun _ => C.g⟩ : Zonotope (Vec ℝ n)).spectraShadow
  -- `sphere + segment`
  sphere.plus segment

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
