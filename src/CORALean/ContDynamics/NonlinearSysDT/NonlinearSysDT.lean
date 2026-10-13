module

public import CORALean.ContSet.ContSet.ContSet

@[expose] public section

/-!
# Discrete-time nonlinear systems: the representation

CORA's `nonlinearSysDT`: `x(k+1) = f(x(k), u(k))`, carrying only the update
map, time-invariant as `NonlinearSys`'s field is. No flow, no time integral and
no `MatExp`: a step is one evaluation of `f`, not a solution of an ODE.

Simpler than `NonlinearSys` for the same reason `LinearSysDT` is simpler than
`LinearSys` — no continuous time to sample and no discretization step, so a
linearization here is already the discrete system a step is taken against.

`Trajectory` mirrors `NonlinearSys.Trajectory` with `step` in place of `flow`,
and `LinearSysDT.Trajectory` with `f` in place of `A x + u`. `TrajectoryOn K`
is the bounded form `LinearSysDT` carries, for the same reason: a run known
only for its first `K` steps.
-/

-- Authors:       Claude Opus 5
-- Written:       04-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinearSysDT (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n

structure NonlinearSysDT.Trajectory (sys : NonlinearSysDT n m) (R₀ : S n) (U : S m)
    (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) : u k ∈ construct U
  step (k : ℕ) : x (k + 1) = sys.f (x k) (u k)

/-- A run known only for its first `K` steps: `x` and `u` past that point are
unconstrained, exactly as `LinearSysDT.TrajectoryOn`'s are. -/
structure NonlinearSysDT.TrajectoryOn (sys : NonlinearSysDT n m) (R₀ : S n) (U : S m)
    (K : ℕ) (x : ℕ → Vec ℝ n) (u : ℕ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (k : ℕ) (hk : k < K) : u k ∈ construct U
  step (k : ℕ) (hk : k < K) : x (k + 1) = sys.f (x k) (u k)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
