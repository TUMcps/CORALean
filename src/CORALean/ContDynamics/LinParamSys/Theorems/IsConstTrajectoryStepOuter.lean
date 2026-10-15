module

public import CORALean.ContDynamics.LinParamSys.Theorems.IsConstTrajectoryTimeIntervalOuter
public import CORALean.ContDynamics.LinParamSys.Theorems.InputSolutionOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInputReflected

@[expose] public section

/-!
# Where a constant-parameter run is at the end of a step

The two halves of a step put together: `timeIntervalStep` for what the initial
set carries and `inputSolution` for what the inputs contributed, both computed
from the matrix set alone. Nothing is assumed of the run beyond the trajectory
itself — the measurability the input solution wants is
`aestronglyMeasurable_input_reflected`, which a trajectory always has.

At the end of the step: `inputSolution_outer` is proved at `r`, so this is the
time-point solution there, enclosed by the time-interval step of the
homogeneous part. `timeInterval_outer_inputSolution` is the same statement at
every `t` of the step, at the cost of `0 ∈ U`.

The three hypotheses on the remainder product are what the input solution asks
of `Mtimes` at an interval matrix, and are properties of a representation.
-/

-- Authors:       Claude Opus 5
-- Written:       08-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of a `'constParam'` run, initial set and inputs together. -/
theorem LinParamSys.IsCanonicalConstTrajectory.step_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : Mat ℝ n n} {r : ℝ}
    (traj : sys.IsCanonicalConstTrajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U))) :
    x r ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) := by -- --- PROOF ---
  have lin := traj.toLinearSys
  -- the input's own domain is the step reflected, which is where `hu` is read
  have hu : ∀ τ ∈ Set.Ioc (0:ℝ) r, u (r - τ) ∈ construct U := fun τ hτ =>
    traj.input _ (hT ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
  have hmeas := lin.aestronglyMeasurable_input_reflected (c := r) (r := r)
    (by rwa [sub_self])
  exact traj.timeInterval_outer hr hT hε hr.le (le_refl r) hbdd
    (sys.inputSolution_outer hr (m + 2) hε traj.param hconv hclosed hbdd
      hRconv hRclosed hRbdd hu hmeas)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
