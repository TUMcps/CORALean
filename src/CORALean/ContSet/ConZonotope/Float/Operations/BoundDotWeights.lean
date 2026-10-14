module

public import CORALean.ContSet.ConZonotope.Float.Operations.NominalBoundWeights
public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot

@[expose] public section

/-!
# `ConZonotope.boundDotWeights`

`nominalBoundWeights` for the nominal set, the error box's own reach added
upward. Sound at every weight vector, so this is where a certificate from any
source, trusted or not, becomes a bound on the stored set.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The bound at any weights, the error box's reach added upward. -/
def ConZonotope.boundDotWeights (cZ : ConZonotope 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ}
    (a : Vec 𝕋 n) (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (y : Vec 𝕋 cZ.P.m) (zu zl : Vec 𝕋 cZ.P.me) : FloatBound 𝕋 cZ.construct c :=
  InflatedContSet.boundOfParts (cZ.nominalBoundWeights a hc y zu zl) (cZ.I_error.boundDot a hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
