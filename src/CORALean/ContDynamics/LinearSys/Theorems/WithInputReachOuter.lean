module

public import CORALean.ContDynamics.LinearSys.Definitions.WithInputReachExact
public import CORALean.ContDynamics.LinearSys.Operations.WithInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.AestronglyMeasurableInput
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindowExact
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachSubsetParticularSolution
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkWrappingFreeOuter
public import CORALean.ContDynamics.LinearSys.Theorems.VariationOfConstants
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reach` with inputs encloses every run, one window at a time

[1, Alg. 2]'s soundness. A run on `[0, tFinal]` is at time `t` at
`e^{At} x(0) + ∫₀ᵗ e^{A(t-s)} u(s) ds` (`variation_of_constants`), and `t` falls
in a window `τ_k` `reach` keeps. The first term is in `H^R(τ_k)`
(`reachStepkWrappingFree_outer`); the second is one admissible input's contribution by `t`,
so in `P^R(t_{k+1})` (`inputReach_subset_particularSolution`, where `0 ∈ U`
is spent). `plus_outer` puts the sum in the window's set.

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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]
variable [∀ n, ConvexSet (S n) (Vec ℝ n)] [∀ n, CompactSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every state a run on `[0, tFinal - tStart]` from `X₀ = params.X₀`, under inputs in
`sys.U`, reaches is in one of `reach`'s windows. -/
theorem LinearSys.WithInput.reach_outer (sys : LinearSys.WithInput 𝕋 S n)
    (params : Reach.Params (S n) ℝ) {options : LinearSys.ReachStepOptions ℝ}
    (hΔt : 0 < options.Δt) : -- --- CONCL ---
    sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct (sys.reach params options) := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tF⟩ := params
  obtain ⟨Δt, η⟩ := options
  unfold LinearSys.WithInput.reach
  dsimp only at *
  generalize tF - tStart = tFinal at *
  rintro _ ⟨x, u, traj, t, ht, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  have htk1 : t ≤ ((k + 1 : ℕ) : ℝ) * Δt := by push_cast; linarith
  -- the order `reach` runs at, `m + 2` in `timeIntervalStep_outer_at`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  -- the run on `[0, t]`, split into its free motion and its input's integral
  have hTt : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 tFinal := Set.Icc_subset_Icc_right ht.2
  have hU : Bornology.IsBounded (construct (construct sys.U)) :=
    CompactSet.isBounded_construct sys.U
  have hvoc := traj.variation_of_constants hTt le_rfl ht.1 hU
  rw [sub_zero] at hvoc
  -- that integral is one admissible input's contribution by `t`
  have hin : (∫ s in (0:ℝ)..t, exp ((t - s) • toRealMat sys.sys.A) *ᵥ u s)
      ∈ sys.sys.inputReach sys.U t :=
    ⟨u, fun s hs => traj.input s (hTt hs), traj.aestronglyMeasurable_input hTt, rfl⟩
  -- window `k` is `H^R(τ_k) ⊕ P^R(t_{k+1})`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hvoc]
    refine Plus.plus_outer _ _ (Set.add_mem_add ?_ ?_)
    · exact sys.sys.reachStepkWrappingFree_outer hΔt hε X₀ hkt htk
        (Set.mem_image_of_mem _ traj.init)
    · exact sys.sys.inputReach_subset_particularSolution hΔt hε sys.zero_mem_U k ht.1 htk1 hin

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
