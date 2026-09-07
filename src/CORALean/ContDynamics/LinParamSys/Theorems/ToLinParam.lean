import CORALean.ContDynamics.LinParamSys.LinParamSys
import CORALean.ContDynamics.LinearSys.LinearSys

/-!
# A continuous-time linear system is one with a set-valued matrix, at a point

`LinearSys`, as the constant-parameter instantiation `A := ofPoint (toRealMat
sys.A)` of `LinParamSys` — CORA's `'constParam'` at the point `sys.A` denotes.
Needs `OfPoint (𝕄 n n) (Mat ℝ n n)` rather than fixing `𝕄 := Mat 𝕋` as
`LinearSysDT.toLinParam` does, so the target can be any set representation,
not only the point-matrix one. The trajectory correspondence is
`TrajectoryToLinParam.lean`.
-/

-- Authors:       Tobias Ladner
-- Written:       07-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)] [OfPoint (𝕄 n n) (Mat ℝ n n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- `LinearSys`, as the constant-parameter instantiation at `sys.A`'s point. -/
def LinearSys.toLinParam (sys : LinearSys 𝕋 n) : LinParamSys 𝕄 n :=
  ⟨OfPoint.ofPoint (toRealMat sys.A)⟩

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
