import CORALean.ContDynamics.NeurNetContrSys.NeurNetContrSys
import Mathlib.Analysis.Matrix.Normed

/-!
# An order admissible for a step and its plant's matrix

`LinearSys.reachOrder`'s formula at `reach_outer`'s own side condition —
`‖Δt • A‖ / (η + 2) < 1` has no `+ 2` on the numerator's denominator here, so
`⌈‖Δt • A‖⌉₊` alone clears it, `reachOrder_admissible` its proof.
-/

-- Authors:       Claude Sonnet 5
-- Written:       24-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order admissible for the step `Δt` at `sys.plant.A`, `η` in
`NeurNetContrSys.reach`'s own naming. -/
noncomputable def NeurNetContrSys.reachOrder (sys : NeurNetContrSys 𝕋 S n) (Δt : ℝ) : ℕ :=
  ⌈‖Δt • toRealMat sys.plant.A‖⌉₊

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
