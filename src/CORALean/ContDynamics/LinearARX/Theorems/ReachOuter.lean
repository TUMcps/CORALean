module

public import CORALean.ContDynamics.LinearARX.Theorems.ToLinearSysDTIsTrajectory
public import CORALean.ContDynamics.LinearSysDT.Theorems.ReachOuter

@[expose] public section

/-!
# The converted system's reach contains every ARX window

`LinearSysDT.reach_outer` along the converted trajectory: the window of outputs
`(y(k), …, y(k+p-1))` lies in the reachable set at step `k`. The set is the
conversion's, with its input set `inputSet U`; reach in the ARX form is separate.

## Inputs
* `sys` – ARX system
* `o` – maximum zonotope order
* `Y₀` – initial window set
* `U` – input set
* `y` – outputs
* `u` – inputs
* `k` – step

## Hypotheses
* `ho` – order positive
* `traj` – ARX trajectory

## Conclusion
* the output window lies in the converted system's reachable set
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   01-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet Scalar Plus Reduce Mtimes

variable {𝕋 : Type} [Scalar 𝕋] [ExactScalar 𝕋] {dy du p : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)] [Mtimes (Mat 𝕋) S]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearARX.reach_outer (sys : LinearARX 𝕋 dy du p) {o : ℕ} (ho : 0 < o)
    (Y₀ : S (p * dy)) (U : S du) {y : ℕ → Vec ℝ dy} {u : ℕ → Vec ℝ du}
    (traj : sys.IsTrajectory Y₀ U y u) (k : ℕ) :
    LinearARX.stack p y k ∈ construct
      (sys.toLinearSysDT.reach ⟨Y₀, sys.inputSet U, 0, k⟩ ⟨o, ho⟩) :=
  sys.toLinearSysDT.reach_outer ho Y₀ (sys.inputSet U) (sys.toLinearSysDT_isTrajectory traj) k

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
