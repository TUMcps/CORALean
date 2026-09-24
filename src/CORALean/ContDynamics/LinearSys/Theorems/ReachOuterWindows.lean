import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
import CORALean.ContDynamics.LinearSys.Operations.Reach
import CORALean.ContDynamics.LinearSys.Theorems.ExistsReachWindow
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinearSys.Theorems.ReachStepkOuter

/-!
# `reach` encloses `reachExact`, one window at a time

A time `t ∈ [0, tFinal]` falls in a window `τ_k` `reach` keeps
(`exists_reach_window`), and `reachStepk_outer` puts `e^{At} x₀` in that
window's set: `e^{At} = e^{A t_k} e^{Aτ}` with `τ = t - t_k ∈ [0, Δt]`. The
order is `reach`'s own, `reachOrder_admissible`'s.
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

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)]
variable [Mtimes (Mat ℝ) S] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal]`,
is in one of `reach`'s windows. -/
theorem LinearSys.reach_outer (sys : LinearSys 𝕋 n) {tFinal Δt : ℝ} {η : ℕ} (hΔt : 0 < Δt)
    (X₀ : S n) : sys.reachExact tFinal (construct X₀)
      ⊆ construct (sys.reach tFinal Δt η X₀) := by -- --- PROOF ---
  rintro _ ⟨t, ht, x₀, hx₀, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := LinearSys.exists_reach_window hΔt ht
  -- the order `reach` runs at, `m + 2` in `timeIntervalStep_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  -- window `k` holds `e^{At} x₀`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · exact sys.reachStepk_outer hΔt hε X₀ hkt htk (Set.mem_image_of_mem _ hx₀)

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
