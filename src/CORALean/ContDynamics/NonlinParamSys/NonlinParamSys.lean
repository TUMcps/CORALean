module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Continuous-time nonlinear systems with uncertain parameters

CORA's `nonlinParamSys`: `ẋ(t) = f(x(t), u(t), p(t))` with the output equation `y = g(x, u, p)`,
`NonlinearSys` with a third argument ranging over a parameter set of dimension `q`. Two
readings, as CORA distinguishes them: `IsTrajectory` lets `p` vary freely over time;
`IsConstTrajectory` fixes one `p ∈ construct P` for the whole run. Every constant trajectory is
a time-varying one (`isConstTrajectory_toIsTrajectory`); the converse fails and is not stated.
`NonlinearSys.toNonlinParam` and `NonlinParamSys.toNonlinearSys` are the two embeddings. Both
are Carathéodory runs, so a jumping input or parameter is admissible; [1, Def. 1] states the
reachable set for Lipschitz-continuous inputs and time-varying `p(t) ∈ P`.

## References

* [1] M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Nonlinear Systems with
      Uncertain Parameters using Conservative Linearization". In Proc. of the 47th IEEE
      Conference on Decision and Control (CDC), 2008, pp. 4042-4048.
-/

-- Authors:       Claude Opus 5, Claude Opus 5.5
-- Written:       07-September-2026
-- Last update:   18-October-2026
-- Reviewed:      19-October-2026 (Tobias Ladner)


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open ContSet MeasureTheory

variable {n m q : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

/-- A nonlinear system `ẋ = f(x, u, p)` with an uncertain parameter `p`, as CORA's `nonlinParamSys`;
the output `g` has dimension `r`. -/
structure NonlinParamSys (n m q : ℕ) where
  f : Vec ℝ n → Vec ℝ m → Vec ℝ q → Vec ℝ n
  r : ℕ
  g : Vec ℝ n → Vec ℝ m → Vec ℝ q → Vec ℝ r

/-- A Carathéodory run on `T` in which the parameter may change at every instant: inputs lie in `U`,
the parameter in `P`, the state integrates `f`, and the output follows `g`. -/
structure NonlinParamSys.IsTrajectory (sys : NonlinParamSys n m q) (T : Set ℝ)
    (R₀ : S n) (U : S m) (P : S q) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (p : ℝ → Vec ℝ q) (y : ℝ → Vec ℝ sys.r) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : p t ∈ construct P
  meas : AEStronglyMeasurable (fun t => sys.f (x t) (u t) (p t)) (volume.restrict T)
  integrable (t : ℝ) (ht : t ∈ T) :
    IntervalIntegrable (fun s => sys.f (x s) (u s) (p s)) volume 0 t
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, sys.f (x s) (u s) (p s)
  output (t : ℝ) (ht : t ∈ T) : y t = sys.g (x t) (u t) (p t)

/-- The uncertain-but-constant reading: one `p ∈ construct P` for the whole run,
rather than a fresh one at every instant. -/
structure NonlinParamSys.IsConstTrajectory (sys : NonlinParamSys n m q) (T : Set ℝ)
    (R₀ : S n) (U : S m) (P : S q) (x : ℝ → Vec ℝ n) (u : ℝ → Vec ℝ m)
    (p : Vec ℝ q) (y : ℝ → Vec ℝ sys.r) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : p ∈ construct P
  meas : AEStronglyMeasurable (fun t => sys.f (x t) (u t) p) (volume.restrict T)
  integrable (t : ℝ) (ht : t ∈ T) : IntervalIntegrable (fun s => sys.f (x s) (u s) p) volume 0 t
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, sys.f (x s) (u s) p
  output (t : ℝ) (ht : t ∈ T) : y t = sys.g (x t) (u t) p

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
