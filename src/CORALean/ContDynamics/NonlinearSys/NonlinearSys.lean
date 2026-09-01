import CORALean.ContSet.ContSet.API

/-!
# Continuous-time nonlinear systems: the representation

CORA's `nonlinearSys`: `ẋ(t) = f(x(t), u(t))`, carrying only the vector field.
Time-invariant, as CORA's is — a time-varying field is this with time carried in
the state.

State and input dimensions are separate, which CORA's are and `LinearSys`'s are
not: there the input enters additively and so has to match the state.

`Trajectory` mirrors `LinearSys.Trajectory` field for field — the same
forward-time derivative within `Set.Ici 0`, the same reading of the input set as
covering disturbances — so the two agree by definition at a linear field, which
is `LinearSys.trajectory_iff_nonlinearSys`.

No reachability yet. That needs an abstraction error, which is where CORA's
conservative linearization begins and where the next development goes.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure NonlinearSys (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n

structure NonlinearSys.Trajectory (sys : NonlinearSys n m) (R₀ : S n) (U : S m)
    (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : 0 ≤ t) : u t ∈ construct U
  flow (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt x (sys.f (x t) (u t)) (Set.Ici 0) t

end CORALean.Real
