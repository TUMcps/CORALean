module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# A Taylor order the float enclosures of `e^{At}` admit at every member

`LinearSys.OrderAdmissibleFloat` with the system's whole interval matrix in
place of a point one: `η` is at least `2`, and the float norm bound of
`[tLo, tHi] · sys.A` over `η + 2` is at most `1/2`, so the float remainder is
sound at every member and every time of the range.

## Inputs
* `sys` – interval-matrix system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order

## Output
* `η` is at least 2 and the float remainder bound at the time range is sound
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `η` is at least `2` and the float remainder bound at `[tLo, tHi] · sys.A`
is sound at it. -/
def LinParamSys.OrderAdmissibleFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (tLo tHi : 𝕋) (η : ℕ) : Prop :=
  2 ≤ η ∧ toReal (MatExp.normUpperBound (Interval.smul tLo tHi sys.A)) / ((η : ℝ) + 2) ≤ 1 / 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
