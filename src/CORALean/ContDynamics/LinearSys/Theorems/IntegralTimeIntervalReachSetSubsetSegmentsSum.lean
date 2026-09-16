import CORALean.ContDynamics.LinearSys.Theorems.IntegralReachSetEq
import CORALean.ContDynamics.LinearSys.Theorems.IntegralTimeIntervalReachSetEqUnion
import CORALean.ContDynamics.LinearSys.Theorems.InputReachMono
import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetInputSolution
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalStepOuterSegments

/-!
# The integral time-interval reachable set inside an exact sum, not a representation

The `IntegralTrajectory` counterpart of `timeIntervalReachSet_subset_segments_sum`, built on
`integralReachSet_eq` in place of `variation_of_constants`/`inputSolution_timeInterval_outer`:
each `t ∈ [0, r]` restricts the ambient run to `Icc 0 t` (`aux_integralTrajectory_restrict`),
where `integralReachSet_eq` names `x t` exactly, and `inputReach_mono` moves its input part up
to `t = r` before `inputReach_subset_inputSolution` encloses it — no `AEStronglyMeasurable`
step of the run's own input is needed, since `IntegralTrajectory.meas` already is one.
-/

-- Authors:       Tobias Ladner
-- Written:       16-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix Pointwise ContSet Scalar NormedSpace MeasureTheory

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

omit [∀ n, Plus (S n) (Vec ℝ n)] [Mtimes (Mat ℝ) S] [Mtimes ℐ S] in
/-- A run on `T` is a run on any smaller domain, `IntegralTrajectory`'s own
`Trajectory.restrict`: every field either drops or shrinks with the domain. -/
theorem aux_integralTrajectory_restrict {sys : LinearSys 𝕋 n} {T T' : Set ℝ} {R₀ U : S n}
    {x u : ℝ → Vec ℝ n} (traj : sys.IntegralTrajectory T R₀ U x u) (hT : T' ⊆ T) :
    sys.IntegralTrajectory T' R₀ U x u where
  init := traj.init
  input t ht := traj.input t (hT ht)
  meas := traj.meas.mono_measure (Measure.restrict_mono hT le_rfl)
  cont := traj.cont.mono hT
  flow t ht := traj.flow t (hT ht)


-- =======================================  MAIN THEOREM  ======================================= --

-- unfolds every hypothesis the two lemmas it composes need at once
set_option maxHeartbeats 1000000 in
/-- Reach for this to enclose the whole interval's integral reachable set by a genuine sum of
segments and sets. -/
theorem LinearSys.integralTimeIntervalReachSet_subset_segments_sum (sys : LinearSys 𝕋 n)
    {T : Set ℝ} (R₀ U : S n) {r : ℝ} (hr : 0 < r) (hT : Set.Icc 0 r ⊆ T) {m : ℕ}
    (hε : ‖r • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U))
    (hRconv : Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRclosed : IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (hRbdd : Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (toRealMat sys.A) r (m + 2)) U)))
    (h0 : (0 : Vec ℝ n) ∈ construct U) :
    sys.integralTimeIntervalReachSet T R₀ U r
      ⊆ segments (construct R₀) ((exp (r • toRealMat sys.A)).mulVecLin '' construct R₀)
        + construct (Mtimes.mtimes (𝕄 := ℐ)
            (MatExp.correctionMatrix (toRealMat sys.A) r (m + 2)) R₀)
        + construct (sys.inputSolution r (m + 2) U) := by -- --- PROOF ---
  rw [sys.integralTimeIntervalReachSet_eq_iUnion]
  refine Set.iUnion₂_subset fun t ht => ?_
  have hTt : Set.Icc (0:ℝ) t ⊆ T := fun s hs => hT ⟨hs.1, le_trans hs.2 ht.2⟩
  rintro _ ⟨x, u, traj, rfl⟩
  have hmem : x t ∈ sys.integralReachSet (Set.Icc 0 t) R₀ U t :=
    ⟨x, u, aux_integralTrajectory_restrict traj hTt, rfl⟩
  rw [sys.integralReachSet_eq R₀ U ht.1 hbdd, Set.mem_add] at hmem
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, w, hw, heq⟩ := hmem
  rw [← heq]
  exact Set.add_mem_add
    (sys.timeIntervalStep_outer_segments hr hε R₀ ht.1 ht.2 (Set.mem_image_of_mem _ hx₀))
    (sys.inputReach_subset_inputSolution hr (m + 2) hε hconv hclosed hbdd hRconv hRclosed hRbdd
      (sys.inputReach_mono hbdd h0 ht.1 ht.2 hw))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
