import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionTimeIntervalOuter

/-!
# A trajectory stays in the step enclosure, inputs and all

The closed form splits a run into what the initial set carries and what the
inputs contributed, and the two are enclosed separately: `timeIntervalStep` for
the first, and a set the caller supplies for the second.

The input enclosure is a hypothesis here, and `timeInterval_outer_inputSolution`
discharges it: `t` ranges over the whole step, so one set has to cover every `t`
at once, which is Althoff's Prop. 3.3 and costs `0 ∈ U` on top of what the
sampled version needs.

Integrability is not a hypothesis: `InputIntegrable` derives it from `U` being
bounded, which every representation of a set of points is.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [OuterContSet S ℝ]
variable [Mtimes IntervalMat S]

set_option maxHeartbeats 1000000 in
theorem LinearSys.Trajectory.timeInterval_outer {sys : LinearSys 𝕋 n} {R₀ U Ud : S n}
    {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u) (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hU : Bornology.IsBounded (construct U))
    (hUd : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.A) *ᵥ u s) ∈ construct Ud) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀) Ud) := by
  have hvoc := traj.variation_of_constants (le_refl (0:ℝ)) ht0
    (traj.intervalIntegrable_input (le_refl (0:ℝ)) ht0 hU)
  rw [sub_zero] at hvoc
  rw [hvoc]
  refine OuterContSet.plus_outer _ _ (Set.add_mem_add ?_ hUd)
  exact sys.timeIntervalStep_outer hr hε R₀ ht0 htr
    (Set.mem_image_of_mem _ traj.init)

set_option maxHeartbeats 40000 in
/-- The same, with the input set named rather than assumed. `0 ∈ U` is what buys
a single enclosure for the whole step; everything else is a property of `U` that
a representation supplies. -/
theorem LinearSys.Trajectory.timeInterval_outer_inputSolution {sys : LinearSys 𝕋 n}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {r : ℝ} (traj : sys.Trajectory R₀ U x u)
    (hr : 0 < r) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes
      (IntervalMat.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    x t ∈ construct (OuterContSet.plus (sys.timeIntervalStep r (m + 2) R₀)
      (sys.inputSolution r (m + 2) U)) :=
  traj.timeInterval_outer hr hε ht0 htr hbdd
    (traj.inputSolution_timeInterval_outer hr (m + 2) hε hconv hclosed hbdd
      hRconv hRclosed hRbdd h0 ht0 htr)

end CORALean.Real
