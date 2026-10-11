import CORALean.ContDynamics.LinearSys.LinearSys
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The input is measurable, with nothing assumed of it

`u` is measurable on any window the domain covers: `meas` is the statement over
all of `T`, and a window inside `T` carries a smaller measure. `InputSolutionTimeIntervalOuter`
composes this with `inputReach_mono`, and `InputSolutionTimeIntervalOuterSplit`
subtracts the piece before an intermediate time from it.
-/

-- Authors:       Tobias Ladner
-- Written:       19-August-2026
-- Last update:   10-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open Matrix ContSet Scalar MeasureTheory

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem LinearSys.Trajectory.aestronglyMeasurable_input {sys : LinearSys 𝕋 n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {a b : ℝ} (traj : sys.Trajectory T R₀ U x u)
    (hT : Set.Icc a b ⊆ T) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) :=
  traj.meas.mono_measure (Measure.restrict_mono hT le_rfl)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
