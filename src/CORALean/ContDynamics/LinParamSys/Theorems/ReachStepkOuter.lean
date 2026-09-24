import CORALean.ContDynamics.LinParamSys.Operations.ReachStepk
import CORALean.ContDynamics.LinParamSys.Theorems.ExpMemExpEnclosure
import CORALean.ContDynamics.LinParamSys.Theorems.TimeIntervalStepOuter

/-!
# One window of `reachUnion` encloses every member's flow over it

`LinearSys.reachStepk_outer` at a member `A` of `sys.A`: at `t ∈ τ_k`,
`e^{At} x₀ = e^{A t_k} (e^{A(t - t_k)} x₀)`; the inner point is in `H^R(τ_0)`
(`timeIntervalStep_outer`, at the same member) and `e^{A t_k}` is in
`expEnclosure` (`exp_mem_expEnclosure`), so `mtimes_outer` puts the product in
the window's set.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]
variable [∀ n, Plus (S n) (Vec ℝ n)] [∀ n, LinComb (S n) (Vec ℝ n)] [Mtimes ℐ S]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under a member's flow, at every time of the
window `τ_k`, is in `reachStepk`'s set for it. -/
theorem LinParamSys.reachStepk_outer (sys : LinParamSys ℐ n) {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖(Interval.smul Δt sys.A).absMax‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n)
    {A : Mat ℝ n n} (hA : A ∈ construct sys.A) {k : ℕ} {t : ℝ}
    (hkt : (k : ℝ) * Δt ≤ t) (htk : t - k * Δt ≤ Δt) :
    (fun x₀ => exp (t • A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.reachStepk Δt (m + 2) X₀ k) := by -- --- PROOF ---
  rintro _ ⟨x₀, hx₀, rfl⟩
  -- `τ = t - t_k ∈ [0, Δt]`, so `H^R(τ_0)` holds `e^{Aτ} x₀`
  have hτ := sys.timeIntervalStep_outer hΔt hε X₀ hA (sub_nonneg.mpr hkt) htk
    (Set.mem_image_of_mem _ hx₀)
  -- `e^{At} = e^{A t_k} e^{Aτ}`, both powers of the same member
  have hc : Commute (((k : ℝ) * Δt) • A) ((t - k * Δt) • A) :=
    ((Commute.refl _).smul_left _).smul_right _
  have hexp : exp (t • A) *ᵥ x₀
      = exp (((k : ℝ) * Δt) • A) *ᵥ (exp ((t - k * Δt) • A) *ᵥ x₀) := by
    have h := exp_add_of_commute hc
    rw [← add_smul, add_sub_cancel] at h
    rw [Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x₀) h
  -- window `k` is `e^{[A] t_k} H^R(τ_0)`, and `e^{A t_k}` is one of its matrices
  show exp (t • A) *ᵥ x₀ ∈ construct (Mtimes.mtimes (𝕄 := ℐ) _ _)
  rw [hexp]
  exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion
    (sys.exp_mem_expEnclosure _ (m + 2) hA) (Set.mem_image_of_mem _ hτ))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
