module

public import CORALean.ContDynamics.LinParamSys.LinParamSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntervalEnclosureFloat
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# `[e^{At}]` over a float time range, at every member of the system's set

`LinearSys.expIntervalFloat` at the system's interval matrix rather than a
point one: `MatExp.expIntervalEnclosure` of the box `[tLo, tHi] · sys.A`,
stored. The float counterpart of `LinParamSys.expEnclosure`, its order given
rather than raised; `reachOrderFloat` finds one that is admissible.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `[e^{At}]` for every `A ∈ sys.A` and `t ∈ [tLo, tHi]`, at Taylor order `η`. -/
def LinParamSys.expIntervalFloat (sys : LinParamSys (fun m n => Interval (Mat 𝕋 m n)) n)
    (tLo tHi : 𝕋) (η : ℕ) : Interval (Mat 𝕋 n n) :=
  let At := Interval.smul tLo tHi sys.A                         -- [t A], t ∈ [tLo, tHi]
  (MatExp.expIntervalEnclosure At η).materialiseMat              -- [e^{tA}]

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
