module

public import CORALean.ContDynamics.LinearSys.Definitions.StepSets
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpEnclosureFuelFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalConstCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.IntervalCorrectionMatrixEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContDynamics.LinearSys.Operations.ExpSquaringFloat
public import CORALean.ContDynamics.LinearSys.Operations.HalvingsFloat
public import CORALean.ContDynamics.LinearSys.Operations.InputSolutionEntrywiseFloat
public import CORALean.ContDynamics.LinearSys.Operations.OneStepClosedForm
public import CORALean.ContSet.Zonotope.Float.Operations.Point

@[expose] public section

/-!
# `LinearSys.oneStepClosedFormFloat`

`LinearSys.oneStepClosedForm` [1] in `𝕋`, one `let` per `let` of the real one, at the order
`ηe ≥ η` with `‖|A|Δt‖ ≤ (ηe + 2)/2` that every sum runs to. The entrywise remainder
`W ≥ E(Δt,ηe)`, the tail of `e^{|A|Δt}` past `ηe`, widens `[F]`, `[G]` and the input solutions,
as `E` does in CORA, but not `[e^{AΔt}]`: for a stiff `A`, `e^{|A|Δt}` grows where `e^{AΔt}` decays.
`[e^{AΔt}]` is `expSquaringFloat` at order `16`, with `s` halvings from `halvingsFloat`. `[F]` and
`[G]` hold the interpolation errors by `expDiff_mem_intervalCorrectionMatrixEntrywise` and its
twin. Every product is `Zonotope.mtimesIntervalMat`; `none` means no admissible order below
`η + expEnclosureFuel` or no `s < 128` with `‖AΔt‖ / 2^s ≤ 1/2`. [2, Eq. 2]: `oneStepFloat`'s bound.

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
  let W := MatExp.expRemainderEntrywise sys.A Δt ηe ηe                    -- `E(Δt,ηe)`
  let s ← sys.halvingsFloat Δt                                            -- halvings of `AΔt`
  let eAdt := sys.expSquaringFloat Δt Δt 16 s                             -- `[e^{AΔt}]`
  let PU := sys.inputSolutionEntrywiseFloat Δt ηe W U                      -- time-varying input
  let Pu := sys.inputSolutionEntrywiseFloat Δt ηe W (Zonotope.point u)     -- constant input
  let C_input := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                -- `[G] u`
    (ContSet := 𝒵[𝕋]) (MatExp.intervalConstCorrectionMatrixEntrywise A Δt ηe W)
    (Zonotope.point u)
  let Htp := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                    -- `[e^{AΔt}] X ⊕ Pu`
    (ContSet := 𝒵[𝕋]) eAdt X ⊞ Pu
  let C_state := Mtimes.mtimes (𝕄 := ℐ[𝕋])                                -- `[F] X`
    (ContSet := 𝒵[𝕋]) (MatExp.intervalCorrectionMatrixEntrywise A Δt ηe W) X
  let Hti := LinComb.linComb X Htp ⊞ C_state                              -- `CH(X, Htp) ⊕ C_state`
  pure ⟨Htp ⊞ PU, Hti ⊞ PU ⊞ C_input⟩                                     -- `Rtp`, `Rti`

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
