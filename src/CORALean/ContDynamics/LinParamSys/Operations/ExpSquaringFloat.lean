module

public import CORALean.ContDynamics.LinParamSys.Operations.ExpIntervalFloat

@[expose] public section

/-!
# `[e^{At}]` by scaling and squaring at every member, over a float time range

`LinearSys.expSquaringFloat` at the system's interval matrix: `expIntervalFloat`
at the range halved `s` times, then `s` interval squarings, each stored. A
squaring of the box holds `e^{2tA}` for every member `A` because the member is
the same in both factors — the constant-parameter reading, `IsConstTrajectory`.

## Inputs
* `sys` – system
* `tLo` – lower time bound
* `tHi` – upper time bound
* `η` – Taylor order
* `s` – number of squarings

## Output
* float interval matrix enclosing the exponential over the time range
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{At}]` for every `A ∈ sys.A` and `t ∈ [tLo, tHi]`: the order-`η` enclosure at
`[tLo, tHi]/2^s`, squared `s` times. -/
def LinParamSys.expSquaringFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (tLo tHi : 𝕋) (η s : ℕ) : Interval (Mat 𝕋 n n) :=
  let B := sys.expIntervalFloat (half^[s] tLo) (half^[s] tHi) η          -- [e^{A t/2^s}]
  (fun P => (Interval.matMul P P).materialiseMat)^[s] B                  -- squared s times

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
