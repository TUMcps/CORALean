module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A nonlinear system is one with an ignored parameter

`ẋ = f(x, u)` is the field `f(x, u, p) = f(x, u)`. Here rather than in
`NonlinearSys`, so that deleting this directory leaves the plain nonlinear
development standing — the conversion belongs to the more general
representation. The guarantee that trajectories agree is
`TrajectoryToNonlinParam.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The field a plain nonlinear system is, its parameter ignored. -/
def NonlinearSys.toNonlinParam (sys : NonlinearSys n m) : NonlinParamSys n m q :=
  ⟨fun x u _ => sys.f x u⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
