module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Continuous-time nonlinear systems: the representation

CORA's `nonlinearSys`: `ẋ(t) = f(x(t), u(t))` with the output equation `y = g(x, u)`,
time-invariant as CORA's is — a time-varying field is this with time in the state. The output
dimension `q` is a field, as CORA's `nrOfOutputs` is a property; absent an output equation
CORA's is the state, `g x u = x`. The output of a run is `g (x t) (u t)`, a function of it, so
`IsTrajectory` does not repeat it. A run reaches `LinearSys` through `linearize` and an
`AbstractionError` certificate.

State and input dimensions are separate, as CORA's are; a run is linearized to `LinearSys`'s
canonical form, whose input is in state coordinates.

`IsTrajectory` is classical and mirrors `LinearSys.IsCanonicalClassicalTrajectory` field for
field — `LinearSys.isCanonicalClassicalTrajectory_iff_nonlinearSys`;
`IsCanonicalClassicalTrajectory.trajectory` carries a run to `LinearSys.IsCanonicalTrajectory`. A
bounded `T` makes `linearize` one step.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       01-September-2026
-- Last update:   14-October-2026
-- Reviewed:      15-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure NonlinearSys (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n
  q : ℕ
  g : Vec ℝ n → Vec ℝ m → Vec ℝ q

structure NonlinearSys.IsTrajectory (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  flow (t : ℝ) (ht : t ∈ T) :
    HasDerivWithinAt x (sys.f (x t) (u t)) T t

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
