module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Continuous-time nonlinear systems: the representation

CORA's `nonlinearSys`: `ẋ(t) = f(x(t), u(t))` with the output equation `y = g(x, u)`,
time-invariant as CORA's is. The output dimension `q` is a field; absent an output equation
CORA's is the state, `g x u = x`. `IsTrajectory` is a Carathéodory run, the integral equation
`x t = x 0 + ∫₀ᵗ f(x s, u s) ds` rather than a derivative at every point (Sontag, *Math.
Control Theory*, Def. C.2.1): a zero-order-hold input has no derivative at a jump. [1, Def. 1]
asks for Lipschitz-continuous inputs, whose runs are classical as well
(`IsTrajectory.hasDerivWithinAt`); `IsTrajectory.of_hasDerivWithinAt` is the converse bridge.
`IsTrajectory.linearize` hands a run to `LinearSys`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       01-September-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A nonlinear system `ẋ = f(x, u)` with output `g` of dimension `q`, as CORA's `nonlinearSys`. -/
structure NonlinearSys (n m : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ n
  q : ℕ
  g : Vec ℝ n → Vec ℝ m → Vec ℝ q

/-- A Carathéodory run on `T` from `R₀` under inputs in `U`. -/
structure NonlinearSys.IsTrajectory (sys : NonlinearSys n m) (T : Set ℝ) (R₀ : S n)
    (U : S m) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m) (y : ℝ → Vec ℝ sys.q) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  meas : AEStronglyMeasurable (fun t => sys.f (x t) (u t)) (volume.restrict T)
  integrable (t : ℝ) (ht : t ∈ T) :
    IntervalIntegrable (fun s => sys.f (x s) (u s)) volume 0 t
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, sys.f (x s) (u s)
  output (t : ℝ) (ht : t ∈ T) : y t = sys.g (x t) (u t)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
