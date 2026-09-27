import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
import CORALean.ContSet.Interval.Float.Operations.Point
import CORALean.ContSet.Interval.Float.Operations.Smul

/-!
# `[e^{At}]` over a float time range

The matrix every float step multiplies by: the float `MatExp.expIntervalEnclosure`
at the interval matrix `[tLo, tHi] · A`, so one box holds `e^{At}` for every `t`
in the range. A range, not a time, because a time `k Δt` a float cannot hold is
only known to lie between two it can: `reachStepkWrappingFreeFloat` encloses `e^{A t_k}`
that way, sound at every float `Δt`. Stored once, since a step reads every entry
`h` times and the enclosure would otherwise be recomputed on each read.
-/

-- Authors:       Tobias Ladner
-- Written:       25-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{At}]` for every `t ∈ [tLo, tHi]`, at Taylor order `η`. -/
def LinearSys.expIntervalFloat (sys : LinearSys 𝕋 n) (tLo tHi : 𝕋) (η : ℕ) :
    Interval (Mat 𝕋 n n) :=
  let At := Interval.smul tLo tHi (Interval.point sys.A)        -- [t A], t ∈ [tLo, tHi]
  (MatExp.expIntervalEnclosure At η).materialiseMat              -- [e^{tA}]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
