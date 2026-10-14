module

public import CORALean.ContSet.InflatedContSet.Operations.Bound
public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.ConPolyZono.Float.Operations.NominalSupportBound
public import CORALean.ContSet.Conversion.Real.Operations.ConPolyZono_to_PolyZonotope

@[expose] public section

/-!
# `ConPolyZono.supportBound` over a floating-point scalar

CORA's `supportFunc_` (type `upper`) for a constrained polynomial zonotope: the nominal part's
bound, whose dependent range bound `u` under the constraints is an argument as over ℝ, and the
error box's own bound, added upward. An upper bound only: the `le` field of the returned
`FloatBound` is the outer theorem.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def ConPolyZono.supportBound (cPZ : ConPolyZono 𝕋 (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal cPZ).polyZonotope.point ''
      {α | (∀ k, |α k| ≤ 1) ∧ (InflatedContSet.nominal cPZ).satisfies α}) c) :
    FloatBound 𝕋 cPZ.construct c :=
  boundOfParts (cPZ.nominalSupportBound a hc u) (cPZ.I_error.boundDot a hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
