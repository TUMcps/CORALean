import CORALean.ContSet.ContSet.API

/-!
# Discrete-time linear systems: the representation

CORA's `linearSysDT`: `x(k+1) = A x(k) + u(k)`, carrying only the matrix.

`Trajectory` is what such a system denotes and the only place the dynamics
appear — one admissible run, with an input per step, so a disturbance is one
too.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure LinearSysDT (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSysDT.Trajectory (sys : LinearSysDT 𝕋 n) (R₀ U : S n)
    (x u : ℕ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = toRealMat sys.A *ᵥ x k + u k

end CORALean.Real
