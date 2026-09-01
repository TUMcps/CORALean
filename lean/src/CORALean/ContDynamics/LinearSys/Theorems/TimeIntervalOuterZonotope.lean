import CORALean.ContDynamics.LinearSys.Theorems.TrajectoryTimeIntervalOuter
import CORALean.ContSet.Zonotope.Real.API

/-!
# The step enclosure at a zonotope, over the whole step

`timeInterval_outer_inputSolution` with the representation substituted in, as
`ReachOuterZonotope` does for the sample times. The same three zonotope lemmas
discharge all six properties of `U` and of the remainder product.

`0 ∈ U` does not follow from being a zonotope and stays a hypothesis, which is
the same split Althoff makes: the thesis treats an input set containing the
origin and one not containing it as separate cases, and only the first has a
single enclosure for the whole step.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]

set_option maxHeartbeats 40000 in
/-- Every trajectory whose initial and input sets are zonotopes stays in the
step enclosure at every time of the step, not only at its end. -/
theorem LinearSys.Trajectory.timeInterval_outer_zonotope {sys : LinearSys 𝕋 n}
    {R₀ U : Zonotope n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer_inputSolution hr hε ht0 htr
    U.convex_construct U.isClosed_construct U.isBounded_construct
    (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U).convex_construct
    (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U).isClosed_construct
    (Mtimes.mtimes (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U).isBounded_construct
    h0

end CORALean.Real
