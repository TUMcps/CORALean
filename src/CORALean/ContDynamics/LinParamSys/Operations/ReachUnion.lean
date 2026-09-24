import CORALean.ContDynamics.LinParamSys.Definitions.ReachParams
import CORALean.ContDynamics.LinParamSys.Operations.ReachOrder
import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep
import CORALean.ContSet.SetUnion.SetUnion

/-!
# `timeIntervalStep`, packaged as `Reach`'s `SetUnion`

One branch, `sys.timeIntervalStep p.r` at `reachOrder`'s own order — the
`Reach.reach` field of the instance, exactly `LinearSys.reachUnion`'s shape.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- One branch, `sys.timeIntervalStep p.r` at `reachOrder`'s own order. -/
noncomputable def LinParamSys.reachUnion (sys : LinParamSys ℐ n) (p : LinParamSys.ReachParams)
    (X₀ : S n) : SetUnion (S n) :=
  ⟨[sys.timeIntervalStep p.r (sys.reachOrder p.r + 2) X₀]⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
