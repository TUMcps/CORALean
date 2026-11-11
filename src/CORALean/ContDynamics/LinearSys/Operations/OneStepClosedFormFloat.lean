module

public import CORALean.ContDynamics.LinearSys.Definitions.StepSets
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpEnclosureFuelFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedForm
public import CORALean.ContSet.Zonotope.Float.Operations.Point

@[expose] public section

/-!
# `LinearSys.oneStepClosedFormFloat`

`LinearSys.oneStepClosedForm` [1] in `𝕋`, one `let` per `let` of the real one. The entrywise
remainder `W ≥ E(Δt,η)` comes from an enclosure of `e^{|A|Δt}` at the first order `ηe ≥ η` with
`‖|A|Δt‖ ≤ (ηe + 2)/2`, and `[e^{AΔt}]` is the series of `AΔt` widened by `[-W, W]`. `[F]` and `[G]`
hold the interpolation errors by `expDiff_mem_intervalCorrectionMatrixEntrywise` and
`expIntegralDiff_mem_intervalConstCorrectionMatrixEntrywise`. Every product is
`Zonotope.mtimesIntervalMat`, and `none` means no order below `η + expEnclosureFuel` is admissible.
The evaluation order is that of the `let`s and of `expIntervalTaylor`, `sumDown`/`sumUp` and
`inputTaylorSumFloat`; [2, Eq. 2] is the scalar bound of `oneStepFloat`.

## Inputs
* `sys` – linear system
* `X` – start float zonotope
* `U` – input float zonotope
* `u` – float constant input
* `Δt` – float step length
* `η` – Taylor order

## Output
* float time-point and time-interval sets of the step, none if the exponential cannot be enclosed

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../references/2023/wetzlinger-fully-automated-verification.md)
* [2] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../references/2014/althoff-tac-nonlinear-dae.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- CORA's `oneStep`, one block, in floats and in closed form. -/
def LinearSys.oneStepClosedFormFloat (sys : LinearSys 𝕋 n) (X U : Zonotope (Vec 𝕋 n)) (u : Vec 𝕋 n)
    (Δt : 𝕋) (η : ℕ) : Option (LinearSys.StepSets (Zonotope (Vec 𝕋 n))) := do
  let A := Interval.point sys.A                                           -- [A, A]
  let B := Interval.smul Δt Δt (Interval.point (Interval.magnitudeMat A)) -- [|A|Δt]
  let ηe ← MatExp.admissibleOrder (MatExp.normUpperBound B) η MatExp.expEnclosureFuel
  let W := MatExp.expRemainderEntrywise sys.A Δt η ηe                     -- `E(Δt,η)`
  let PU := sys.inputSolutionEntrywiseFloat Δt η W U                      -- time-varying input
  let Pu := sys.inputSolutionEntrywiseFloat Δt η W (Zonotope.point u)     -- constant input
  let C_input := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                -- `[G] u`
    (ContSet := 𝒵[𝕋]) (MatExp.intervalConstCorrectionMatrixEntrywise A Δt η W)
    (Zonotope.point u)
  let Htp := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                    -- `[e^{AΔt}] X ⊕ Pu`
    (ContSet := 𝒵[𝕋]) (sys.expEntrywiseFloat Δt η W) X ⊞ Pu
  let C_state := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                -- `[F] X`
    (ContSet := 𝒵[𝕋]) (MatExp.intervalCorrectionMatrixEntrywise A Δt η W) X
  let Hti := LinComb.linComb X Htp ⊞ C_state                              -- `CH(X, Htp) ⊕ C_state`
  pure ⟨Htp ⊞ PU, Hti ⊞ PU ⊞ C_input⟩                                     -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
