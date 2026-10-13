module

public import CORALean.ContSet.HPolytope.Real.HPolytope
public import CORALean.Global.LinProg.Duality

@[expose] public section

/-!
# A halfspace description's own construct is `Feasible`
-/

-- Authors:       Claude Opus 5
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]


-- =======================================  MAIN THEOREM  ======================================= --

theorem HPolytope.construct_eq_feasible (P : HPolytope α) :
    P.construct = Feasible P.A P.b P.Ae P.be := rfl

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
