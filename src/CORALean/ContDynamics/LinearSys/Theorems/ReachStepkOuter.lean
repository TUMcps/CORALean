import CORALean.ContDynamics.LinearSys.Operations.ReachStepk
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter

/-!
# One window of `reach` holds the homogeneous flow over the whole window

By induction on `k`. Window `0` is `timeIntervalStep_outer`. At a time `t` of
window `k + 1`, `e^{At} = e^{AΔt} e^{A(t - Δt)}`, where `t - Δt` lies in window
`k`, whose set holds `e^{A(t - Δt)} x₀` by the induction hypothesis;
`mtimes_outer` carries it to `R(τ_{k+1}) = e^{AΔt} R(τ_k)`. The statement is
`reachStepkWrappingFree_outer`'s, word for word.
-/

-- Authors:       Tobias Ladner
-- Written:       27-September-2026
-- Last update:   ---
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

/-- Every image of the initial set under the flow, at every time of the window
`τ_k`, is in `reachStepk`'s set for it. -/
theorem LinearSys.reachStepk_outer (sys : LinearSys 𝕋 n) {Δt : ℝ} (hΔt : 0 < Δt) {m : ℕ}
    (hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) (X₀ : S n) {k : ℕ} {t : ℝ}
    (hkt : (k : ℝ) * Δt ≤ t) (htk : t - k * Δt ≤ Δt) :
    (fun x₀ => exp (t • toRealMat sys.A) *ᵥ x₀) '' construct X₀
      ⊆ construct (sys.reachStepk Δt (m + 2) X₀ k) := by -- --- PROOF ---
  induction k generalizing t with
  | zero =>
    -- window `0` is `timeIntervalStep` itself
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hkt htk
    exact sys.timeIntervalStep_outer hΔt hε X₀ hkt htk
  | succ k ih =>
    rintro _ ⟨x₀, hx₀, rfl⟩
    push_cast at hkt htk
    -- `t - Δt` is in window `k`, whose set holds `e^{A(t - Δt)} x₀`
    have hprev := ih (t := t - Δt) (by linarith) (by linarith) (Set.mem_image_of_mem _ hx₀)
    -- `e^{At} = e^{AΔt} e^{A(t - Δt)}`, both powers of the same matrix
    have hc : Commute (Δt • toRealMat sys.A) ((t - Δt) • toRealMat sys.A) :=
      ((Commute.refl _).smul_left _).smul_right _
    have hexp : exp (t • toRealMat sys.A) *ᵥ x₀ = exp (Δt • toRealMat sys.A)
        *ᵥ (exp ((t - Δt) • toRealMat sys.A) *ᵥ x₀) := by
      have h := exp_add_of_commute hc
      rw [← add_smul, add_sub_cancel] at h
      rw [Matrix.mulVec_mulVec]
      exact congrArg (· *ᵥ x₀) h
    -- window `k + 1` is `e^{AΔt} R(τ_k)`
    show exp (t • toRealMat sys.A) *ᵥ x₀ ∈ construct (Mtimes.mtimes _ _)
    rw [hexp]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hprev))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
