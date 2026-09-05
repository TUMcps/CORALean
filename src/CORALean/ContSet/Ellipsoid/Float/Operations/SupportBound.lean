import CORALean.ContSet.Ellipsoid.Float.Operations.NominalBoundDot
import CORALean.ContSet.InflatedContSet.Operations.Bound
import CORALean.ContSet.Interval.Float.Operations.BoundDot

/-!
# An ellipsoid answers a direction in floats, and still without a linear program

The exact value is `⟨d, q⟩ + ‖Gᵀd‖₂`, and the norm is a square root the scalar
has not got. It needs none: the caller hands in a proposed length `s`, and
`Global.Float.EuclideanNorm` turns `s` into a bound by one multiplication in
each rounding direction, so an ellipsoid costs the layer no new scalar operation.

The whole set's bound adds the nominal bound and the error box's own, upward.
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}

/-- The whole set: the nominal bound and the error box's own, added upward. -/
def Ellipsoid.boundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (sqSumUp (E.pullbackAbs a)) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 E.construct c :=
  InflatedContSet.boundOfParts (E.nominalBoundDot a hc s hs) (E.err.boundDot a hc)

end CORALean.Float
