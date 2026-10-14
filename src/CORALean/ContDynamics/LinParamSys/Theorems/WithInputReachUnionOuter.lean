module

public import CORALean.ContDynamics.LinParamSys.Definitions.WithInputReachUnionExact
public import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachUnion
public import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
public import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolution
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkOuter
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
public import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContDynamics.LinearSys.Operations.Canonical
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reachUnion` with inputs encloses every constant-parameter run

[1, Alg. 4]'s soundness, `0 ∈ U`. A run fixes one member `A`, and
is the point system `⟨A⟩`'s run (`toLinearSys`), so at `t` it is at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds`. `t` falls in a window `τ_k`; the first
term is in `H^R(τ_k)` (`reachStepk_outer`), the second in `P^R(t_{k+1})`
(`inputReach_subset_particularSolution`, where `0 ∈ U` is spent), both at `A`.

## References

* [1] M. Althoff. "Reachability Analysis and its Application to the Safety
      Assessment of Autonomous Cars". PhD thesis, TU München, 2010.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   30-September-2026
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a constant-parameter run on `[0, tFinal - tStart]` from `R0`, under
inputs in `sys.U`, reaches is in one of `reachUnion`'s windows. -/
theorem LinParamSys.WithInput.reachUnion_outer (sys : LinParamSys.WithInput S n)
    (params : Reach.Params (S n) ℝ) {options : LinearSys.ReachStepOptions ℝ}
    (hΔt : 0 < options.Δt) :
    sys.reachUnionExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct (sys.reachUnion params options) := by -- --- PROOF ---
  rintro _ ⟨A, x, u, traj, t, ht, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * options.Δt := by push_cast; linarith
  -- the order `reachUnion` runs at, `m + 2` in `reachStepk_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max options.η (sys.sys.reachOrder options.Δt + 2) = m + 2 :=
    ⟨max options.η (sys.sys.reachOrder options.Δt + 2) - 2, by omega⟩
  have hε : ‖(Interval.smul options.Δt sys.sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hadm := sys.sys.reachOrder_admissible options.Δt
    have hle : ((sys.sys.reachOrder options.Δt + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hm ▸ le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) hadm
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have trajL := traj.toLinearSys
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 (params.tFinal - params.tStart) :=
    Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct sys.U)) :=
    CompactSet.isBounded_construct sys.U
  have hvoc := trajL.variation_of_constants hTt le_rfl ht.1 hU
  simp only [sub_zero, Scalar.toRealMat_real] at hvoc
  -- that integral is one admissible input's contribution by `t`, under `A`
  have hin : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ (LinearSys.canonical A : LinearSys ℝ n).inputReach sys.U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), trajL.aestronglyMeasurable_input hTt, by
      simp only [Scalar.toRealMat_real]⟩
  -- window `k` is `H^R(τ_k) ⊕ P^R(t_{k+1})`, and `k < N`
  refine SetUnion.mem_construct.mpr
    ⟨sys.reachStepk options.Δt (m + 2) params.X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc]
    refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · exact sys.sys.reachStepk_outer hΔt hε params.X₀ traj.param hkt htk
        (Set.mem_image_of_mem _ traj.init)
    · exact sys.sys.inputReach_subset_particularSolution hΔt hε traj.param sys.zero_mem_U
        k ht.1 htk1 hin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
