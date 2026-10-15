module

public import CORALean.ContDynamics.NeurNetContrSys.Operations.Augment
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# An order admissible for a step and the augmented matrix

`LinearSys.reachOrder`'s formula at `reach_outer`'s own side condition, read at the matrix the
steps are taken with, the augmented `A_aug = [A B; 0 0]` (`augment`) —
`‖Δt • A_aug‖ / (η + 2) < 1` has no `+ 2` on the numerator's denominator here, so
`⌈‖Δt • A_aug‖⌉₊` alone clears it, `reachOrder_admissible` its proof.
-/

-- Authors:       Claude Sonnet 5, Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =====================================  MAIN DEFINITION  ====================================== --

/-- An order admissible for the step `Δt` at the augmented matrix `[A B_nn; 0 0]`, `η` in
`NeurNetContrSys.reach`'s own naming. -/
noncomputable def NeurNetContrSys.reachOrder (sys : NeurNetContrSys (LinearSys 𝕋 n) S n)
    (Δt : ℝ) : ℕ :=
  ⌈‖Δt • sys.augment.A‖⌉₊

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
