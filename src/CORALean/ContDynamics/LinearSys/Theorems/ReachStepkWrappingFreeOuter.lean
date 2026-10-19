module

public import CORALean.ContDynamics.LinearSys.Operations.ReachStepkWrappingFree
public import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter

@[expose] public section

/-!
# One window of `reachWrappingFree` holds the homogeneous flow over the whole window

At a time `t ∈ [t_k, t_k + Δt]`, `e^{At} = e^{A t_k} e^{Aτ}` with
`τ = t - t_k ∈ [0, Δt]`: `timeIntervalStep_outer_at` puts `e^{Aτ} x₀` in `R(τ_0)`,
and `mtimes_outer` carries it to `R(τ_k) = e^{A t_k} R(τ_0)`. The window-level
fact both `LinearSys.reachWrappingFree_outer` and `LinearSys.WithInput.reach_outer` are
assembled from.
-/

-- Authors:       Claude Opus 5.5
-- Written:       24-September-2026
-- Last update:   ---
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

/-- Every image of the initial set under the flow, at every time of the window
`τ_k`, is in `reachStepkWrappingFree`'s set for it. -/
theorem LinearSys.reachStepkWrappingFree_outer (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n) {k : ℕ} {t : ℝ}
    (hkt : (k : ℝ) * Δt ≤ t) (htk : t - k * Δt ≤ Δt) : -- --- CONCL ---
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.reachStepkWrappingFree Δt (m + 2) X₀ k) := by -- --- PROOF ---
  rintro _ ⟨x₀, hx₀, rfl⟩
  -- `τ = t - t_k ∈ [0, Δt]`, so `R(τ_0)` holds `e^{Aτ} x₀`
  have hτ := sys.timeIntervalStep_outer_at hΔt hε X₀ (sub_nonneg.mpr hkt) htk
    (Set.mem_image_of_mem _ hx₀)
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same matrix
  have hc : Commute (((k : ℝ) * Δt) • toRealMat sys.A) ((t - k * Δt) • toRealMat sys.A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (t • toRealMat sys.A) *ᵥ x₀ = exp (((k : ℝ) * Δt) • toRealMat sys.A)
      *ᵥ (exp ((t - k * Δt) • toRealMat sys.A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  -- window `k` is `e^{A t_k} R(τ_0)`
  show exp (t • toRealMat sys.A) *ᵥ x₀ ∈ construct (Mtimes.mtimes _ _)
  rw [hexp]
  exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hτ))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
