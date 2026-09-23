import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# The linear system a linearization leaves behind

`linearize`: fresh rather than `NonlinearSys.linearize`, whose target
`LinearSys` carries a flow this system has none of.
-/

-- Authors:       Tobias Ladner
-- Written:       04-September-2026
-- Last update:   06-September-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The linear system a linearization at any matrix `A` leaves behind. Fresh
rather than `NonlinearSys.linearize`, whose target `LinearSys` carries a flow
this system has none of. -/
def NonlinearSysDT.linearize (A : Mat ℝ n n) : LinearSysDT ℝ n := ⟨A⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
