import CORALean.ContDynamics.LinParamSys.Definitions.WithInputReachUnionExact
import CORALean.ContDynamics.LinParamSys.Operations.WithInputReachUnion
import CORALean.ContDynamics.LinParamSys.Theorems.ConstTrajectoryToLinearSys
import CORALean.ContDynamics.LinParamSys.Theorems.InputReachSubsetParticularSolution
import CORALean.ContDynamics.LinParamSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinParamSys.Theorems.ReachStepkOuter
import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
import CORALean.ContDynamics.LinearSys.Theorems.InputIntegrable
import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants

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

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   24-September-2026
-- Last revision: ---


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

/-- Every state a constant-parameter run on `[0, p.tFinal]` from `X₀`, under
inputs in `sys.U`, reaches is in one of `reachUnion`'s windows. -/
theorem LinParamSys.WithInput.reachUnion_outer (sys : LinParamSys.WithInput S n)
    (p : LinearSys.ReachParams) (X₀ : S n) :
    sys.reachUnionExact p (construct X₀) ⊆ construct (sys.reachUnion p X₀) := by -- --- PROOF ---
  rintro _ ⟨A, x, u, traj, t, ht, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window p.hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * p.Δt := by push_cast; linarith
  -- the order `reachUnion` runs at, `m + 2` in `reachStepk_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max p.η (sys.sys.reachOrder p.Δt + 2) = m + 2 :=
    ⟨max p.η (sys.sys.reachOrder p.Δt + 2) - 2, by omega⟩
  have hε : ‖(Interval.smul p.Δt sys.sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 := by
    have hadm := sys.sys.reachOrder_admissible p.Δt
    have hle : ((sys.sys.reachOrder p.Δt + 2 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
      exact_mod_cast hm ▸ le_max_right _ _
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by linarith)) hadm
  -- the run is the point system `⟨A⟩`'s, split into its free motion and its input's integral
  have trajL := traj.toLinearSys
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 p.tFinal := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct sys.U)) :=
    CompactSet.isBounded_construct sys.U
  have hvoc := trajL.variation_of_constants hTt ht.1 (trajL.intervalIntegrable_input hTt ht.1 hU)
  simp only [sub_zero, Scalar.toRealMat_real] at hvoc
  -- that integral is one admissible input's contribution by `t`, under `A`
  have hin : (∫ s in (0:ℝ)..t, exp ((t - s) • A) *ᵥ u s)
      ∈ (LinearSys.mk A : LinearSys ℝ n).inputReach sys.U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), trajL.aestronglyMeasurable_input hTt, by
      simp only [Scalar.toRealMat_real]⟩
  -- window `k` is `H^R(τ_k) ⊕ P^R(t_{k+1})`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk p.Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc]
    refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · exact sys.sys.reachStepk_outer p.hΔt hε X₀ traj.param hkt htk
        (Set.mem_image_of_mem _ traj.init)
    · exact sys.sys.inputReach_subset_particularSolution p.hΔt hε traj.param sys.zero_mem_U
        k ht.1 htk1 hin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
