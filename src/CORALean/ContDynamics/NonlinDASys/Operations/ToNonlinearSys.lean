module

public import CORALean.ContDynamics.NonlinDASys.Definitions.ReducedModel
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# The reduced ordinary system

`ẋ = f(x, h(x,u), u)`: the algebraic variable eliminated through the reduced model.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n p m : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The ordinary system with `y` replaced by `h x u`. -/
def NonlinDASys.ReducedModel.toNonlinearSys {sys : NonlinDASys n p m}
    (red : sys.ReducedModel) : NonlinearSys n m :=
  ⟨fun x u => sys.f x (red.h x u) u⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
