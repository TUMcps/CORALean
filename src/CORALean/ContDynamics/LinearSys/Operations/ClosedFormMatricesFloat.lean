module

public import CORALean.ContDynamics.LinearSys.Definitions.ClosedFormMatrices
public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedFormFloat
public import CORALean.ContSet.Interval.Float.Operations.MaterialiseMat

@[expose] public section

/-!
# The matrices of a closed-form step, in floats

`[e^{AΔt}]`, `[F]`, `[G]` and the remainder `W` as `LinearSys.oneStepClosedFormFloat` forms them,
at the order, remainder and halvings of the zonotope step, materialised once.

## Inputs
* `sys` – linear system
* `Δt` – float step length
* `η` – Taylor order

## Output
* the matrices; none if no admissible order or no halving encloses the exponential
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       13-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The matrices of the closed-form step; none if no admissible order or no halving encloses the
exponential. -/
def LinearSys.closedFormMatricesFloat (sys : LinearSys 𝕋 n) (Δt : 𝕋) (η : ℕ) :
    Option (LinearSys.ClosedFormMatrices 𝕋 n) := do
  let A := Interval.point sys.A                                           -- [A, A]
  let B := Interval.smul Δt Δt (Interval.point (Interval.magnitudeMat A)) -- [|A|Δt]
  let ηe ← MatExp.admissibleOrder (MatExp.normUpperBound B) η MatExp.expEnclosureFuel
  let W := (Interval.point (MatExp.expRemainderEntrywise sys.A Δt ηe ηe)).materialiseMat.inf
  let s ← sys.halvingsFloat Δt                                            -- halvings of `AΔt`
  pure ⟨ηe, W, (sys.expSquaringFloat Δt Δt 16 s).materialiseMat,          -- `E(Δt,ηe)`, `[e^{AΔt}]`
    (MatExp.intervalCorrectionMatrixEntrywise A Δt ηe W).materialiseMat,  -- `[F]`
    (MatExp.intervalConstCorrectionMatrixEntrywise A Δt ηe W).materialiseMat⟩  -- `[G]`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
