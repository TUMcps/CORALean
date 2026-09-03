import CORALean.ContSet.ContSet.ContSet

/-!
# Continuous-time nonlinear systems: the representation

CORA's `nonlinearSys`: `ẋ(t) = f(x(t), u(t))`, carrying only the vector field.
Time-invariant, as CORA's is — a time-varying field is this with time carried in
the state. CORA's class also carries an output equation `y = g(x, u)`, which has
no counterpart here, as it has none for `LinearSys`.

State and input dimensions are separate, which CORA's are and `LinearSys`'s are
not: there the input enters additively and so has to match the state.

`Trajectory` mirrors `LinearSys.Trajectory` field for field — the same time
domain `T` carrying the derivative, the same reading of the input set as
covering disturbances — so the two agree by definition at a linear field, which
is `LinearSys.trajectory_iff_nonlinearSys`. A bounded `T` is what makes
`linearize` a one-step statement.

Reachability is not here and is not its own algorithm: an `AbstractionError`
certificate turns a run of this system into a run of a linear one, and
`LinearSys` does the rest.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   03-September-2026
-- Last revision: ---

namespace CORALean.Real

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]

structure NonlinearSys (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n

structure NonlinearSys.Trajectory (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (sys.f (x t) (u t)) T t

end CORALean.Real
