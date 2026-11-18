module

public import CORALean.ContDynamics.LinearSys.Definitions.VerifyKrylovWindow
public import CORALean.Global.EuclideanNorm
public import CORALean.Global.Float.SoundFloatArithmetic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

/-!
# What the restart windows of a Krylov verification must satisfy

Window `i` starts at `o_i Δt`, `o_i` the steps of the windows before it, and covers `steps_i Δt`:
at every `τ ∈ [0, steps_i Δt]`, `w' e^{(o_i Δt + τ) A} = ν_i V_i e^{τ H_i} e₁ + e` with
`‖e‖₂ ≤ err_i`. CORA.cpp's `KrylovWindows` builds them (Arnoldi restarted from the approximate
state at the start of a window, its error carried by a Gershgorin or Lyapunov weight); that
construction is not formalized here, so a Krylov verification takes this as a hypothesis.

## Inputs
* `A` – real system matrix
* `w` – real direction
* `Δt` – step size of the pass
* `wins` – the windows

## Output
* whether every window approximates `w' e^{tA}` over its times within its error
-/

-- Authors:       Claude Opus 5.5
-- Written:       18-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Float SoundFloatArithmetic Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {𝕋 : Type} [FloatOps 𝕋] [SoundFloatArithmetic 𝕋] {n : ℕ}


-- =====================================  MAIN DEFINITION  ====================================== --

/-- Every window `i` holds `w' e^{tA}` within `err_i` over `[o_i Δt, (o_i + steps_i) Δt]`. -/
def LinearSys.IsVerifyKrylovWindows (A : Mat ℝ n n) (w : Vec ℝ n) (Δt : ℝ)
    (wins : List (LinearSys.VerifyKrylovWindow 𝕋 n)) : Prop :=
  ∀ i (hi : i < wins.length), ∀ τ : ℝ, 0 ≤ τ → τ ≤ (wins[i].steps : ℝ) * Δt →
    ∃ e : Vec ℝ n, ‖e‖₂ ≤ toReal wins[i].err ∧
      w ᵥ* exp ((((wins.take i).map (·.steps)).sum * Δt + τ) • A)
        = toReal wins[i].ν • (toRealMat wins[i].V *ᵥ
          (exp (τ • toRealMat wins[i].H) *ᵥ fun l => if l.val = 0 then 1 else 0)) + e

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
