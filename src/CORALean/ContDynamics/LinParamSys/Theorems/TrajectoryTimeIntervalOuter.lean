import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryToLinearSys
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

/-!
# A time-varying run stays in the step enclosure, the drift paid as input

`ConstTrajectory.timeInterval_outer` at `'varParam'`. The homogeneous half is
unchanged — `timeIntervalStep` is the box's and knows no member, so freezing
`Â ∈ construct sys.A` costs nothing there. What changes is the second half:
`Trajectory.toLinearSys` turns the parameter mismatch into input, so the set
`Vd` has to hold the drift `(A s - Â) x s` as well as `u s`, integrated against
the frozen exponential.

This is not CORA's `'varParam'` branch. `Interval.matPow` admits a different
member at each factor, which is tighter than freezing one and paying the
mismatch; `Trajectory.timeIntervalStep_outer` proves *that* set sound for an
input-free run, through a Peano–Baker expansion. This is the enclosure freezing
gives, sound at every `Â` at once and with an input, which that one is not.

`Â` is a free choice; the box's centre makes the drift smallest, its radius
bounding `‖A s - Â‖` uniformly.
-/

-- Authors:       Tobias Ladner
-- Written:       08-September-2026
-- Last update:   02-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

-- the closed form is read at the point system the frozen matrix names
set_option maxHeartbeats 400000 in
/-- One step of a `'varParam'` run: the box's homogeneous step, plus whatever
holds the input and the parameter drift together. -/
theorem LinParamSys.Trajectory.timeInterval_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U V Vd : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n} {r : ℝ}
    (traj : sys.Trajectory T R₀ U x u A) (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {Â : Mat ℝ n n} (hÂ : Â ∈ construct sys.A)
    (hV : ∀ s ∈ T, (A s - Â) *ᵥ x s + u s ∈ construct V)
    (hVb : Bornology.IsBounded (construct V)) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r)
    (hVd : (∫ s in (0:ℝ)..t, exp ((t - s) • Â) *ᵥ ((A s - Â) *ᵥ x s + u s))
      ∈ construct Vd) :
    x t ∈ construct (Plus.plus (sys.timeIntervalStep r (m + 2) R₀) Vd) := by -- --- PROOF ---
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 htr⟩
  -- the run is a point system's run at `Â`, its input enlarged by the drift
  have lin := traj.toLinearSys Â hV
  have hvoc := lin.variation_of_constants hTt ht0 (lin.intervalIntegrable_input hTt ht0 hVb)
  simp only [Scalar.toRealMat_real, sub_zero] at hvoc
  rw [hvoc]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ hVd)
  exact sys.timeIntervalStep_outer hr hε R₀ hÂ ht0 htr (Set.mem_image_of_mem _ traj.init)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
