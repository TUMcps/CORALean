import CORALean.ContDynamics.LinParamSysDT.LinParamSysDT
import CORALean.ContDynamics.LinearSysDT.LinearSysDT

/-!
# A discrete-time linear system is one with a set-valued matrix

`LinearSysDT`, as the point instantiation `𝕄 := Mat 𝕋` of `LinParamSysDT`. Here
rather than in `LinearSysDT`, so deleting this directory leaves the
point-matrix development standing. The guarantee that trajectories agree is
`TrajectoryToLinParam.lean`.

#29's open question is whether `LinearSysDT` should be *replaced* by
`LinParamSysDT (Mat 𝕋)` rather than sit beside it — a refactor across ten
downstream files, Tobias's call, not made here. This bridge is the evidence
that the generalization is faithful, so that call can be made on cost rather
than on doubt.
-/

-- Authors:       Tobias Ladner
-- Written:       06-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `LinearSysDT`, as the point-matrix instantiation `𝕄 := Mat 𝕋`. -/
def LinearSysDT.toLinParam (sys : LinearSysDT 𝕋 n) : LinParamSysDT (Mat 𝕋) n := ⟨sys.A⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
