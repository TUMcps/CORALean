import CORALean.ContDynamics.LinParamSys.Operations.TimeIntervalStep
import CORALean.ContDynamics.LinParamSys.Theorems.TrajectoryExistsIntegralEq
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExistsMemIntervalCorrectionMatrixOfIntegral

/-!
# An input-free time-varying run stays in the box's step, unwidened

`LinParamSys.timeIntervalStep_outer` at `'varParam'`: a fresh `A t ∈ sys.A` at
every instant, and still the same set — `CH(X₀, e^{[A]r} X₀) ⊕ F X₀` with the
box's exponential enclosure and correction matrix, CORA's `initReach` for
`linParamSys`, `expmIndMixed` and `priv_tie`. Nothing is frozen and no drift is
paid as input, which `Trajectory.timeInterval_outer` needs.

The run solves the integral equation at a measurable member of the box
(`Trajectory.exists_integral_eq`), and the Peano–Baker expansion of that equation
puts it, at every time of the step, on the interpolation from its start to a
member of the enclosure plus a member of `F` applied to its start
(`MatExp.exists_mem_intervalCorrectionMatrix_of_integral`).

Input-free only; with an input, `…TimeIntervalStepOuterInputSolution`. The float step
is `…TimeIntervalStepFloatOuter`.
-/

-- Authors:       Claude Opus 5.5
-- Written:       02-October-2026
-- Last update:   10-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- An input-free `'varParam'` run is, at every time of the step, in the box's
own time-interval step of the initial set. -/
theorem LinParamSys.Trajectory.timeIntervalStep_outer {sys : LinParamSys ℐ n} {T : Set ℝ}
    {R₀ U : S n} {x u : ℝ → Vec ℝ n} {A : ℝ → Mat ℝ n n}
    (traj : sys.Trajectory T R₀ U x u A) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T)
    (hu : ∀ s ∈ Set.Ico 0 r, u s = 0) {m : ℕ}
    (hε : ‖(Interval.smul r sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    x t ∈ construct (sys.timeIntervalStep r (m + 2) R₀) := by -- --- PROOF ---
  obtain ⟨Â, hÂi, hÂB, hx⟩ := traj.exists_integral_eq hr.le hT hu
  have hxc : ContinuousOn x (Set.Icc 0 r) := traj.cont.mono hT
  obtain ⟨Φ, hΦ, F, hF, heq⟩ :=
    MatExp.exists_mem_intervalCorrectionMatrix_of_integral hÂi hÂB hr hxc hx hε ht0 htr
  have hx₀ := traj.init
  rw [heq]
  refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
  · -- the interpolation, from the start to the start's image under the member `Φ`
    refine LinComb.linComb_outer _ _ ⟨x 0, hx₀, Φ *ᵥ x 0, ?_, 1 - t / r, ?_, ?_⟩
    · exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hΦ (Set.mem_image_of_mem _ hx₀))
    · exact ⟨by linarith [div_le_one_of_le₀ htr hr.le], by linarith [div_nonneg ht0 hr.le]⟩
    · rw [sub_sub_cancel]
  · -- and the correction, the member `F` applied to the start
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion hF (Set.mem_image_of_mem _ hx₀))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
