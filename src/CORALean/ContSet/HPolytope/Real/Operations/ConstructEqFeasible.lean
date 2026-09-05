import CORALean.ContSet.HPolytope.Real.HPolytope
import CORALean.Global.LinProg.Duality

/-!
# A halfspace description's own construct is `Feasible`
-/

-- Authors:       Tobias Ladner
-- Written:       02-September-2026
-- Last update:   05-September-2026
-- Last revision: ---

namespace CORALean.Real

variable {α : Type} [AddCommGroup α] [Module ℝ α]

theorem HPolytope.construct_eq_feasible (P : HPolytope α) :
    P.construct = Feasible P.A P.b P.Ae P.be := rfl

end CORALean.Real
