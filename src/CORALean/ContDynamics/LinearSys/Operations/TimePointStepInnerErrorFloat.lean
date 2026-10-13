module

public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepErrorBoxFloat
public import CORALean.ContDynamics.LinearSys.Operations.TimePointStepExcessFloat

@[expose] public section

/-!
# What a float step owes, for an inner approximation

The budget `timePointStepInnerRepFloat` takes off the float step
`timePointStepInputFloat`: everything the float step holds beyond the exact
held-input step `e^{Ar} X₀ ⊕ (∫₀^r e^{As} ds) U` at the nominal zonotopes of `X₀`
and `U`. Three parts:

* `[e^{Ar}]` applied to `X₀`'s error box, which the exact step at `X₀`'s nominal
  zonotope does not see;
* `timePointStepExcessFloat`, what floats add to the step;
* `timePointStepErrorBoxFloat`, what the exact input solution holds beyond the
  held input.

`timePointStepInputFloat_subset_add_innerErrorFloat` is the guarantee: the float
step lies in the exact held-input step plus this budget. Everything is computed
in `𝕋` and every part is an outer enclosure, so the budget only errs large,
which costs an inner approximation precision and never soundness.
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
  let EX := Mtimes.mtimes (𝕄 := fun m n => Interval (Mat 𝕋 m n))  -- on E(X₀)
    (S := fun k => Zonotope (Vec 𝕋 k)) eAr X₀.E.zonotope
  (EX ⊞ sys.timePointStepExcessFloat r η X₀ U) ⊞                            -- floats' excess
    sys.timePointStepErrorBoxFloat r η U                                    -- P(r) beyond held

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
