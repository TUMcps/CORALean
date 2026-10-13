import CORALean.ContSet.ContSet.ContSet
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous-time nonlinear systems: the representation

CORA's `nonlinearSys`: `ẋ(t) = f(x(t), u(t))`, carrying only the vector field, and
time-invariant as CORA's is — a time-varying field is this with time in the state.

CORA's class also carries an output equation `y = g(x, u)`, which has no
counterpart here for the reason there is no reachability here either: an output
*set* needs an enclosure of `g`, which is the problem of enclosing `f` over again
and gets the same answer. A run reaches `LinearSys` through `linearize` and an
`AbstractionError` certificate, and the linear system's `OutputEq` is what a
specification is checked on.

State and input dimensions are separate, which CORA's are and `LinearSys`'s are
not: there the input enters additively and so has to match the state.

`Trajectory` is classical and mirrors `LinearSys.ClassicalTrajectory` field for
field — `LinearSys.classicalTrajectory_iff_nonlinearSys`; `ClassicalTrajectory.trajectory`
carries a run to `LinearSys.Trajectory`. A bounded `T` makes `linearize` one step.
-/

-- Authors:       Claude Opus 5
-- Written:       01-September-2026
-- Last update:   03-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinearSys (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n

structure NonlinearSys.Trajectory (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (sys.f (x t) (u t)) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
