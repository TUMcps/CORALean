module

public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.NonlinearSys.Definitions.ReachUnionExact
public import CORALean.ContDynamics.NonlinearSys.Operations.ReachUnion
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetExactConfinementOfSubset
public import CORALean.ContDynamics.NonlinearSys.Theorems.ReachSetExactSubsetRelinTimeIntervalHorizon
public import CORALean.ContSet.ContSet.Definitions.Interfaces
public import CORALean.ContSet.Interval.Real.Instances
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# A union `reachUnion` returns contains every state reached within the horizon

The run-time tests are what the proof spends. A returned union means every test passed;
`contains_sound`, `region_subset` and the box inside the ball of radius `2MΔt` turn each into the
ball check `reachSetExact_confinement_of_subset` asks for, the confinement it returns is what
`reachSetExact_subset_relinTimeInterval_horizon` places the reachable set with, and `2MΔt > MΔt`
is the strictness `confined_of_ball` spends. No confinement is assumed of any run. The order is
raised until `reachOrder_admissible` applies at every step; convexity, closedness and
boundedness are the representation's own, `ConvexSet` and `CompactSet`.

## Inputs
* `sys` – system with steps
* `params` – reachability parameters
* `options` – reachability options

## Hypotheses
* none

## Conclusion
* the returned union contains every exact reachable state
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   14-October-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {S Rg : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)] [∀ n, ContSet (Rg n) (Vec ℝ n)]
variable {m n : ℕ}
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [∀ n, Reduce (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [OfInterval S] [Mtimes ℐ S] [∀ n, Contains (Rg n) (S n)]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

theorem NonlinearSys.WithSteps.reachUnion_outer (sys : NonlinearSys.WithSteps S Rg m n)
    (params : Reach.Params (S n) ℝ) (options : LinearSys.ReachOptions ℝ) : -- --- CONCL ---
    ∀ R ∈ sys.reachUnion params options,
      sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
        ⊆ construct R := by -- --- PROOF ---
  intro R (hR : sys.reachUnion params options = some R) y hy
  simp only [NonlinearSys.WithSteps.reachUnion] at hR
  set Δt := options.Δt with hΔtdef
  set N := ⌈(params.tFinal - params.tStart) / Δt⌉₊ with hNdef
  -- the step count divides the horizon, so `hy` is at the horizon `[0, NΔt]`
  split at hR
  case isFalse => exact absurd hR (by simp)
  rename_i hc
  obtain ⟨hΔt, hN, hT, ho⟩ := hc
  rw [← hT] at hy
  split at hR
  case isFalse => exact absurd hR (by simp)
  rename_i hconf
  set q := max options.η ((Finset.range N).sup fun i =>
    (NonlinearSys.linearize (sys.steps i).A).reachOrder Δt) with hq
  -- the order clears every step's matrix
  have hε : ∀ i < N, ‖Δt • (sys.steps i).A‖ / (((q + 2 : ℕ) : ℝ) + 2) < 1 := by
    intro i hi
    refine (NonlinearSys.linearize (sys.steps i).A).reachOrder_admissible Δt ?_
    have hle := Finset.le_sup (f := fun i =>
      (NonlinearSys.linearize (sys.steps i).A).reachOrder Δt) (Finset.mem_range.mpr hi)
    omega
  -- the representation's own convexity, closedness and boundedness
  have hconv : ∀ i < N, Convex ℝ (construct (sys.steps i).linInput) :=
    fun _ _ => ConvexSet.convex_construct _
  have hclosed : ∀ i < N, IsClosed (construct (sys.steps i).linInput) :=
    fun _ _ => (CompactSet.isCompact_construct _).isClosed
  have hbdd : ∀ i < N, Bornology.IsBounded (construct (sys.steps i).linInput) :=
    fun _ _ => (CompactSet.isCompact_construct _).isBounded
  have hRconv : ∀ i < N, Convex ℝ (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (sys.steps i).A Δt (q + 2)) (sys.steps i).linInput)) :=
    fun _ _ => ConvexSet.convex_construct _
  have hRclosed : ∀ i < N, IsClosed (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (sys.steps i).A Δt (q + 2)) (sys.steps i).linInput)) :=
    fun _ _ => (CompactSet.isCompact_construct _).isClosed
  have hRbdd : ∀ i < N, Bornology.IsBounded (construct (Mtimes.mtimes (𝕄 := ℐ)
      (MatExp.inputRemainder (sys.steps i).A Δt (q + 2)) (sys.steps i).linInput)) :=
    fun _ _ => (CompactSet.isCompact_construct _).isBounded
  -- every test passed: the ball of radius `2MΔt` about each start lies in the region
  have hsub : ∀ i < N, ∀ y ∈ construct (sys.sys.relinReach ⟨params.X₀, 0, i⟩
    ⟨Δt, options.ρ, ho⟩ sys.steps (fun i =>
      (NonlinearSys.linearize (sys.steps i).A).inputSolution Δt (q + 2) (sys.steps i).linInput)),
      Metric.closedBall y (2 * sys.M * Δt) ⊆ (sys.steps i).R := by
    intro i hi z hz w hw
    have hc := Contains.contains_sound _ _ (List.all_eq_true.mp hconf i (List.mem_range.mpr hi))
    refine sys.region_subset i (hc (Plus.plus_outer _ _ ⟨z, hz, w - z, ?_, add_sub_cancel z w⟩))
    refine OfInterval.ofInterval_outer _ fun j => ?_
    have hw' : ‖w - z‖ ≤ 2 * sys.M * Δt := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hw
    have hj : ‖(w - z) j‖ ≤ 2 * sys.M * Δt := (norm_le_pi_norm (w - z) j).trans hw'
    exact abs_le.mp (Real.norm_eq_abs _ ▸ hj)
  -- confinement of the whole reachable set, from the ball check
  have hconf' := sys.sys.reachSetExact_confinement_of_subset (T := Set.Icc 0 ((N : ℝ) * Δt))
    params.X₀ sys.U hΔt subset_rfl (q + 2) hε hconv hclosed hbdd hRconv hRclosed hRbdd
    sys.M_pos.le (fun i _ => sys.norm_f_le i) (by nlinarith [sys.M_pos, hΔt]) ho hsub
  -- a run from the bare set `construct R0` is a run from the representation `R0`
  obtain ⟨t, ht, x, u, traj, rfl⟩ := by simpa [NonlinearSys.WithSteps.reachUnionExact] using hy
  have traj' : sys.sys.IsTrajectory (Set.Icc 0 ((N : ℝ) * Δt)) params.X₀ sys.U x u
      (fun t => sys.sys.g (x t) (u t)) :=
    ⟨traj.init, traj.input, traj.meas, traj.integrable, traj.cont, traj.flow, traj.output⟩
  have hx := sys.sys.reachSetExact_subset_relinTimeInterval_horizon params.X₀ sys.U hΔt hN
    subset_rfl hconf' q hε hconv hclosed hbdd (fun i _ => sys.zero_mem_linInput i) hRconv
    hRclosed hRbdd ho ht ⟨x, u, traj', rfl⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  rw [← Option.some_inj.mp hR]
  exact SetUnion.mem_construct_range hi hxi

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
