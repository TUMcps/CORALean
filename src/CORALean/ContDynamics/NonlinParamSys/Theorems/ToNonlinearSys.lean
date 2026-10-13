module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A parametric system is a nonlinear one with the parameter as an input

`w`'s first `m` coordinates read as `u`, its last `q` as `p`: `sys.f` applied to
the two halves `Fin.castAdd` and `Fin.natAdd` split `w` into. The trajectory
correspondence, in both directions, is `TrajectoryToNonlinearSys.lean` and
`TrajectoryOfNonlinearSys.lean`.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The parameter read as the last `q` coordinates of a combined input. -/
def NonlinParamSys.toNonlinearSys (sys : NonlinParamSys n m q) : NonlinearSys n (m + q) :=
  ⟨fun x w => sys.f x (w ∘ Fin.castAdd q) (w ∘ Fin.natAdd m)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
