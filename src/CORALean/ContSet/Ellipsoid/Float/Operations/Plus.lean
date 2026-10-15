module

public import CORALean.ContSet.Ellipsoid.Float.Operations.CenterResidual
public import CORALean.ContSet.Ellipsoid.Float.Operations.GeneratorError
public import CORALean.ContSet.Ellipsoid.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Basic

@[expose] public section

/-!
# `Ellipsoid.plus`

The Minkowski sum of two ellipsoids is not an ellipsoid, so this encloses it and
carries the free parameter every enclosure of it does. Over ℝ that parameter is
Kurzhanski and Varaiya's `l > 0` and the generator matrix is
`[√(1+1/l) G₁ | √(1+l) G₂]`.

Here the parameter is the *two scalings themselves*, `s₁` and `s₂`, which is
what the exact layer already computes with: `l` reaches `plus_outer` only
through them, and the condition they must satisfy is `1/s₁² + 1/s₂² ≤ 1`, which
`l`'s pair meets with equality. Taking the pair widens the family rather than
approximating it. It is a real hypothesis the caller discharges, in the shape of
`HPolytope.boundOfDual`'s dual feasibility: an unverified routine proposes the
two scalings and the inequality is what makes them a bound.

Both blocks concatenate as over ℝ and the generator count adds. Only the center
and the two scalings round, the first into a `residual` and the second into a
`generatorError`, `u` reaching `[-1,1]` in every coordinate.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def Ellipsoid.plus (s₁ s₂ : 𝕋) (E₁ E₂ : Ellipsoid 𝕋 n) : Ellipsoid 𝕋 n where
  k := E₁.k + E₂.k
  c := fun i => addDown (E₁.c i) (E₂.c i)
  G := Ellipsoid.plusG s₁ s₂ E₁ E₂
  I_error := (E₁.I_error.plus E₂.I_error).plus
    ((Ellipsoid.centerResidual E₁.c E₂.c).plus
      (Ellipsoid.generatorError (Ellipsoid.plusGap s₁ s₂ E₁ E₂)))

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
