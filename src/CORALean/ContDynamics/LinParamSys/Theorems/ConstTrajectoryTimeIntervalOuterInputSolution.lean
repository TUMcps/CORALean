import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryInputSolutionTimeIntervalOuter
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryTimeIntervalOuter

/-!
# A constant-parameter run stays in the step enclosure, at every time of the step

`ConstTrajectory.step_outer` holds where the step ends; this holds throughout
it, which is what a time-interval reachable set is. The homogeneous half already
covered every `t ∈ [0, r]`; what was missing was the input half, and
`inputSolution_timeInterval_outer` supplies it.

`0 ∈ U` is the one hypothesis beyond `step_outer`'s, and it is what buys a
single enclosure for the whole step rather than one per time.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- One step of a `'constParam'` run, initial set and inputs together, at every
time of the step rather than at its end. -/
theorem LinParamSys.ConstTrajectory.timeInterval_outer_inputSolution
    {sys : LinParamSys ℐ n} {T : Set ℝ} {R₀ U : S n} {x u : ℝ → Vec ℝ n}
    {A : Mat ℝ n n} {r : ℝ} (traj : sys.ConstTrajectory T R₀ U x u A)
    (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.intervalInputRemainder sys.A r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer hr hT hε ht0 htr hbdd
    (traj.inputSolution_timeInterval_outer hr hT (m + 2) hε hconv hclosed hbdd
      hRconv hRclosed hRbdd h0 ht0 htr)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
