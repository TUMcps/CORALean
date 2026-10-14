module

public import CORALean.ContDynamics.NonlinearSys.Theorems.LinearEmbedding
public import CORALean.ContDynamics.NonlinearSys.Definitions.FloatModel
public import CORALean.ContSet.Interval.Float.Operations.Basic
public import CORALean.ContSet.Interval.Float.Operations.Point

@[expose] public section

/-!
# A linear system as a nonlinear one, for a float run

`LinearSys.nonlinearSys` is `ẋ = A x + u` with a real field, which no float run can evaluate.
`nonlinearSysFloatModel` is its interval extension: `A X ⊕ U` in directed rounding, with the
Jacobian blocks `A` and the identity, each exact in the stored floats. That it encloses the real
system is `nonlinearSysFloatModel_encloses`, so `NonlinearSys.FloatModel.reachFloat` runs the
converted system.
-/

-- Authors:       Claude Opus 5.5
-- Written:       04-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float FloatOps

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

def LinearSys.nonlinearSysFloatModel (sys : LinearSys 𝕋 n) : NonlinearSys.FloatModel 𝕋 n n where
  f := fun X U => (Interval.mtimes sys.A X).plus U
  jacX := fun _ _ => Interval.point sys.A
  jacU := fun _ _ => Interval.point fun i j => if i = j then one else zero

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
