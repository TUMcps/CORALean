import CORALean.Arithmetic.Real.ContSet.ContSet.API

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`: `ẋ(t) = A x(t) + u(t)`, carrying only the matrix.

`Trajectory` is what such a system denotes and the only place the dynamics
appear — one admissible run, with an input at every time, so a disturbance is
one too.

Forward time only, as in `LinearSysDT`, which is why the derivative is one-sided:
`HasDerivWithinAt` on `Set.Ici t` is also the form Mathlib's ODE uniqueness
takes, so a trajectory is usable there as it stands.

`u` carries no regularity hypothesis. It needs none: `x` is differentiable
wherever the flow holds, so `u t = ẋ(t) - A x(t)` is already pinned there.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) n]

structure LinearSys (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSys.Trajectory (sys : LinearSys 𝕋 n) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : 0 ≤ t) : u t ∈ construct U
  flow (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) (Set.Ici t) t

end CORALean.Arithmetic.Real
