module

public import CORALean.ContSet.ContSet.ContSet
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

/-!
# Continuous-time linear systems with a set-valued system matrix

CORA's `@linParamSys`, `ẋ(t) = A x(t) + u(t)` with `A` ranging over a set
`sys.A` — the system-matrix uncertainty CORA calls `type`. `Trajectory` is
`'varParam'`, a fresh `A t ∈ construct sys.A` at every instant; `ConstTrajectory`
is `'constParam'` (CORA's default), one `A ∈ construct sys.A` over the whole flow.
`constTrajectory_toTrajectory` is the direction that always holds; the converse
fails (a run free to vary need not settle on one matrix) and is not stated.

Both are Carathéodory runs, as `LinearSys.Trajectory` is: the integral equation
`x t = x 0 + ∫₀ᵗ (A x + u)`, the form [1, Def. 3.1] writes with the parameter
inside the integral, so a jumping input or parameter is admissible. `meas` and
`measParam` make the input and the parameter measurable on `T`, the signals the
integral is taken of — almost everywhere, which `Trajectory.exists_measurable_param`
sharpens to a parameter measurable and in the box at every instant.

`B` and `c` are absent, as in `LinearSys`: `B U ⊕ c` folds into the input set by
one `mtimes` and one `plus`; unifying that fold for both classes is #59.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5
-- Written:       07-September-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet MeasureTheory

variable {n : ℕ} {𝕄 : ℕ → ℕ → Type} [∀ m n, ContSet (𝕄 m n) (Mat ℝ m n)]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- ========================================  MAIN TYPE  ========================================= --

structure LinParamSys (𝕄 : ℕ → ℕ → Type) (n : ℕ) where
  A : 𝕄 n n

/-- `'varParam'`: a fresh `A t ∈ construct sys.A` at every instant, the flow stated
as the integral equation. -/
structure LinParamSys.Trajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : ℝ → Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param (t : ℝ) (ht : t ∈ T) : A t ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  measParam : AEStronglyMeasurable A (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A s *ᵥ x s + u s)

/-- `'constParam'`: one matrix `A`, fixed over the whole flow, rather than
`Trajectory`'s fresh `A t` at each instant. -/
structure LinParamSys.ConstTrajectory (sys : LinParamSys 𝕄 n) (T : Set ℝ) (R₀ U : S n)
    (x u : ℝ → Vec ℝ n) (A : Mat ℝ n n) : Prop where
  init : x 0 ∈ construct R₀
  input (t : ℝ) (ht : t ∈ T) : u t ∈ construct U
  param : A ∈ construct sys.A
  meas : AEStronglyMeasurable u (volume.restrict T)
  cont : ContinuousOn x T
  flow (t : ℝ) (ht : t ∈ T) : x t = x 0 + ∫ s in (0:ℝ)..t, (A *ᵥ x s + u s)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
