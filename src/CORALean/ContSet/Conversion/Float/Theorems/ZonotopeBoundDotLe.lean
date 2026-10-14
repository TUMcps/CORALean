module

public import CORALean.ContSet.Zonotope.Float.Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Basic
public import CORALean.ContSet.HPolytope.Float.Operations.OfBounds
public import CORALean.ContSet.HPolytope.Float.Operations.Basic
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.Conversion.Float.Operations.Zonotope_to_HPolytope

@[expose] public section

/-!
# A zonotope as halfspaces, over a floating-point scalar

A zonotope answers a direction without a linear program, and this layer computes
that answer with directed rounding: the centre's dot product rounded up, and
each generator's contribution bounded in absolute value.

The absolute value is where a rounding mode has to be chosen twice. A generator's
exact contribution lies between its rounded-down and rounded-up dot products, so
what bounds its magnitude is the larger of the up one and the negated down one —
neither alone would do, the exact value being free to have either sign.
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open Matrix FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n q : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

theorem Zonotope.boundDot_le (Z : Zonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j) :
    ∀ x ∈ Z.construct, c x ≤ toReal (Z.boundDot a hc).val :=
  (Z.boundDot a hc).le

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
