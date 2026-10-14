module

public import CORALean.ContDynamics.NonlinParamSys.NonlinParamSys
public import CORALean.ContDynamics.NonlinearSys.NonlinearSys

@[expose] public section

/-!
# A parametric system is a nonlinear one with the parameter as a state

CORA's standard treatment of an uncertain but constant parameter: `z = (x, p)`,
`ż = (f(x, u, p), 0)`, the parameter `q` extra states that never move. The
first `n` coordinates of `z` read as `x`, the last `q` as `p`, split as
`toNonlinearSys` splits its combined input. A run of this system from a set of
`(x₀, p)` is a constant-parameter run of `sys` read in `n + q` coordinates,
`ConstTrajectoryToAugment.lean`; a time-varying parameter is not one, its
derivative not being zero.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

variable {n m q : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- The parameter read as the last `q` coordinates of the state, with zero dynamics. -/
def NonlinParamSys.augment (sys : NonlinParamSys n m q) : NonlinearSys (n + q) m :=
  ⟨fun z u => Fin.append (sys.f (z ∘ Fin.castAdd q) u (z ∘ Fin.natAdd n)) 0, sys.r,
    fun z u => sys.g (z ∘ Fin.castAdd q) u (z ∘ Fin.natAdd n)⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
