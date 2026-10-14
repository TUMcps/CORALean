module

public import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
public import CORALean.ContDynamics.LinearSys.Operations.ReachWrappingFree
public import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
public import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
public import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkWrappingFreeOuter
public import CORALean.ContSet.SetUnion.Theorems.Basic

@[expose] public section

/-!
# `reachWrappingFree` encloses `reachExact`, one window at a time

A time `t ∈ [0, tFinal]` falls in a window `τ_k` `reachWrappingFree` keeps
(`exists_reach_window`), and `reachStepkWrappingFree_outer` puts `e^{At} x₀` in that
window's set: `e^{At} = e^{A t_k} e^{Aτ}` with `τ = t - t_k ∈ [0, Δt]`. The
order is `reachWrappingFree`'s own, `reachOrder_admissible`'s.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   24-September-2026
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


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal - tStart]`,
is in one of `reachWrappingFree`'s windows. -/
theorem LinearSys.reachWrappingFree_outer (sys : LinearSys 𝕋 n)
    (params : Reach.Params (S n) ℝ) {options : LinearSys.ReachStepOptions ℝ}
    (hΔt : 0 < options.Δt) :
    sys.reachExact (params.tFinal - params.tStart) (construct params.X₀)
      ⊆ construct (sys.reachWrappingFree params options) := by -- --- PROOF ---
  obtain ⟨X₀, tStart, tF⟩ := params
  obtain ⟨Δt, η⟩ := options
  unfold LinearSys.reachWrappingFree
  dsimp only at *
  generalize tF - tStart = tFinal at *
  rintro _ ⟨t, ht, x₀, hx₀, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  -- the order `reachWrappingFree` runs at, `m + 2` in `timeIntervalStep_outer_at`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  -- window `k` holds `e^{At} x₀`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepkWrappingFree Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · exact sys.reachStepkWrappingFree_outer hΔt hε X₀ hkt htk (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
