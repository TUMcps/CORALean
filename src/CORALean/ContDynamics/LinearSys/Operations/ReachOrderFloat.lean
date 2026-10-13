module

public import CORALean.ContDynamics.LinearSys.LinearSys
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.AdmissibleOrderFloat
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.NormUpperBoundFloat
public import CORALean.ContSet.Interval.Float.Operations.Point
public import CORALean.ContSet.Interval.Float.Operations.Smul

@[expose] public section

/-!
# A Taylor order for the float step, raised until admissible

The float counterpart of `reachOrder`: the first order from `max η 2` on at which
`nrm ≤ (η + 2)/2`, `nrm` the float bound `MatExp.normUpperBound` of the interval
matrix `[tLo, tHi] · A`, certified by the float comparison. At a point `t` that
is `max(η, 2, ⌈2 t ‖|A|‖∞⌉ - 2)`, `‖|A|‖∞` the largest row sum of the entries'
magnitudes: the order to give CORA for the same run. The search stops after `4096` orders
and says `none`: a norm past `(max η 2 + 4097)/2`, or one the float format
cannot hold (an overflow, a `NaN`), gets no order rather than an unchecked one.
-/

-- Authors:       Claude Opus 5.5
-- Written:       25-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The first order from `max η 2` the float remainder bound at `[tLo, tHi] · A`
admits, or `none` if none of the next `4096` does. -/
def LinearSys.reachOrderFloat (sys : LinearSys 𝕋 n) (tLo tHi : 𝕋) (η : ℕ) : Option ℕ :=
  let nrm := MatExp.normUpperBound (Interval.smul tLo tHi (Interval.point sys.A))  -- ≥ ‖t A‖
  MatExp.admissibleOrder nrm (max η 2) 4096                          -- η + 2 ≥ 2 nrm, from max η 2

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
