import CORALean.Real.ContDynamics.LinearSys.Theorems.TimeIntervalOuter
import CORALean.Real.ContDynamics.LinearSys.Theorems.InputIntegrable

/-!
# A trajectory stays in the step enclosure, inputs and all

The closed form splits a run into what the initial set carries and what the
inputs contributed, and the two are enclosed separately: `timeIntervalStep` for
the first, and a set the caller supplies for the second.

The input enclosure is a hypothesis, as it is for the sampled version. What
would discharge it is Althoff's Thm. 3.1 — and that needs the input set to be
convex and closed, since an integral is a limit of convex combinations and
lands in the convex hull whatever the set looks like. `ContSet` offers neither,
by design, so the obligation belongs to a representation rather than here.

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
variable {S : ℕ → Type} [∀ n, ContSet (S n) n] [OuterContSet S ℝ]
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

end CORALean.Real
