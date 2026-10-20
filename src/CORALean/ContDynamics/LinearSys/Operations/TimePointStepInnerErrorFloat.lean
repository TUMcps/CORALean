module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorBoxFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepExcessFloat
public import CORALean.ContSet.Conversion.Float.Operations.Interval_to_Zonotope
public import CORALean.ContSet.Conversion.Real.Operations.Interval_to_Zonotope

@[expose] public section

/-!
# What a float step owes, for an inner approximation

The budget `timePointStepInnerRepFloat` takes off the float step `timePointStepInputFloat`:
everything the float step holds beyond the exact held-input step `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U`
at the nominal zonotopes of `X₀` and `U`. Three parts: `[e^{Ar}]` applied to `X₀`'s error box, which
the exact step at `X₀`'s nominal zonotope does not see; `timePointStepExcessFloat`, what floats add
to the step; and `timePointStepErrorBoxFloat`, what the exact input solution holds beyond the held
input. `timePointStepInputFloat_subset_add_innerErrorFloat` is the guarantee. Every part is an outer
enclosure computed in `𝕋`, so the budget only errs large, which costs an inner approximation
precision and never soundness.

## Inputs
* `sys` – linear system
* `r` – float step length
* `η` – Taylor order
* `X₀` – initial float zonotope
* `U` – input float zonotope

## Output
* float zonotope of what the float step holds beyond the exact held-input step
-/

-- Authors:       Claude Opus 5.5
-- Written:       09-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- What the float step from `X₀` holds beyond the exact held-input step at the nominal
zonotopes: `[e^{Ar}]` on `X₀`'s error box, the float excess, and the step's error box. -/
def LinearSys.timePointStepInnerErrorFloat (sys : LinearSys 𝕋 n) (r : 𝕋) (η : ℕ)
    (X₀ U : Zonotope (Vec 𝕋 n)) : Zonotope (Vec 𝕋 n) :=
  let eAr := sys.expIntervalFloat r r η                                     -- [e^{Ar}]
  let EX := Mtimes.mtimes (𝕄 := ℐ[𝕋])  -- on E(X₀)
    (S := 𝒵[𝕋]) eAr X₀.I_error.zonotope
  (EX ⊞ sys.timePointStepExcessFloat r η X₀ U) ⊞                            -- floats' excess
    sys.timePointStepErrorBoxFloat r η U                                    -- P(r) beyond held

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
