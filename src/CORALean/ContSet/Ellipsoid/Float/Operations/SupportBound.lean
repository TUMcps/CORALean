module

public import CORALean.ContSet.Ellipsoid.Float.Operations.NominalBoundDot
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot

@[expose] public section

/-!
# An ellipsoid answers a direction in floats, and still without a linear program

The exact value is CORA's `⟨d, q⟩ + √(dᵀ Q d)`, and the square root is one the scalar need not
take: the caller hands in a proposed length `s`, checked by `dᵀ Q d ≤ s²` from above (`quadUp`)
and one multiplication rounded down, so an ellipsoid costs the layer no new scalar operation.

The whole set's bound adds the nominal bound and the error box's own, upward.

## Inputs
* `E` – ellipsoid
* `c` – linear functional
* `a` – float vector of `c`
* `s` – length bounding `√(aᵀ Q a)`

## Hypotheses
* `hc` – `c x = ∑ aᵢ xᵢ`
* `hs` – `aᵀ Q a ≤ s²`

## Output
* float bound of `c` on the whole set `E`
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       02-September-2026
-- Last update:   15-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The whole set: the nominal bound and the error box's own, added upward. -/
def Ellipsoid.boundDot (E : Ellipsoid 𝕋 n) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ i, toReal (a i) * x i) (s : 𝕋)
    (hs : toReal (E.quadUp a) ≤ toReal (mulDown s s)) :
    FloatBound 𝕋 E.construct c :=
  -- `boundOfParts` spelt out: through it the noncomputable `nominal` would be called
  (E.nominalBoundDot a hc s hs).add (E.I_error.boundDot a hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
