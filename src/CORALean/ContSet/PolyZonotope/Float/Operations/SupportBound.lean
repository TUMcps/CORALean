module

public import CORALean.ContSet.Interval.Float.Operations.BoundDot
public import CORALean.ContSet.PolyZonotope.Float.Operations.NominalSupportBound

@[expose] public section

/-!
# `PolyZonotope.supportBound` over a floating-point scalar

CORA's `supportFunc_` for a polynomial zonotope: the nominal part's bound, whose dependent
range bound `u` is an argument as over ℝ, and the error box's own bound, added upward. An
upper bound only: the `le` field of the returned `FloatBound` is the outer theorem.

## Inputs
* `pZ` – polynomial zonotope
* `c` – linear functional
* `a` – float coefficient vector of the functional
* `u` – support bound of the nominal part

## Hypotheses
* `hc` – the vector represents the functional

## Output
* support bound of the set
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      14-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Float

open FloatOps SoundFloatArithmetic InflatedContSet

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def PolyZonotope.supportBound (pZ : PolyZonotope (Vec 𝕋 n)) {c : Vec ℝ n →ₗ[ℝ] ℝ} (a : Vec 𝕋 n)
    (hc : ∀ x : Vec ℝ n, c x = ∑ j, toReal (a j) * x j)
    (u : FloatBound 𝕋 ((InflatedContSet.nominal pZ).subsetAt {a | ∀ k, |a k| ≤ 1}) c) :
    FloatBound 𝕋 pZ.construct c :=
  boundOfParts (pZ.nominalSupportBound a hc u) (pZ.I_error.boundDot a hc)

end CORALean.Float


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
