module

public import CORALean.ContDynamics.NonlinDASys.Definitions.ReducedModel
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# `ContDynamics/NonlinDASys/Operations`: small declarations

One section per declaration, at most five code lines each; alphabetical, after the
sections each one uses (CONTRIBUTING, "Small declarations").
-/


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --


-- ========================  `NonlinDASys.ReducedModel.toNonlinearSys`  ========================= --
-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   ---
-- Reviewed:      ---

namespace CORALean

variable {n p m : ℕ}

/-- The ordinary system with `y` replaced by `h x u`.

`ẋ = f(x, h(x,u), u)`: the algebraic variable eliminated through the reduced model. -/
def NonlinDASys.ReducedModel.toNonlinearSys {sys : NonlinDASys n p m}
    (red : sys.ReducedModel) : NonlinearSys n m :=
  ⟨fun x u => sys.f x (red.h x u) u⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
