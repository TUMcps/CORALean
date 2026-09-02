import CORALean.ContSet.ContSet.ContSet

/-!
# Continuous-time linear systems: the representation

CORA's `linearSys`: `ẋ(t) = A x(t) + u(t)`, carrying only the matrix.

`Trajectory` is what such a system denotes and the only place the dynamics
appear — one admissible run, with an input at every time, so a disturbance is
one too.

The time domain `T` is a parameter: `Set.Ici 0` is a run over all forward time,
`Set.Icc 0 τ` one over a bounded horizon, which is what a one-step method and a
hybrid location both need. The derivative is taken within `T` itself — two-sided
wherever `T` is, one-sided at an endpoint. Within `Ici t` it would be a right
derivative everywhere, which does not force continuity, and a run free to jump
is not a trajectory.

`init` stays unconditional, so `x 0` is the initial state whether or not `0 ∈ T`.

`u` needs no regularity hypothesis: `x` is differentiable wherever the flow
holds, so `u t = ẋ(t) - A x(t)` is already pinned there, which is enough to
integrate it — see `InputIntegrable`.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   02-September-2026
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure LinearSys (𝕋 : Type) (n : ℕ) where
  A : Mat 𝕋 n n

structure LinearSys.Trajectory (sys : LinearSys 𝕋 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (toRealMat sys.A *ᵥ x t + u t) T t

end CORALean.Real
