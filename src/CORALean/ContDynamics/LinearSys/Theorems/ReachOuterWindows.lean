import CORALean.ContDynamics.LinearSys.Definitions.ReachExact
import CORALean.ContDynamics.LinearSys.Operations.Reach
import CORALean.ContDynamics.LinearSys.Theorems.ReachOrderAdmissible
import CORALean.ContDynamics.LinearSys.Theorems.TimeIntervalOuter

/-!
# `reach` encloses `reachExact`, one window at a time

A time `t ∈ [0, tFinal]` falls in the window `τ_k` with `k = ⌈t / Δt⌉ - 1`, one
`reach` keeps. There `e^{At} = e^{A t_k} e^{Aτ}` with `τ = t - t_k ∈ [0, Δt]`:
`timeIntervalStep_outer` puts `e^{Aτ} x₀` in `R(τ_0)`, and `mtimes_outer`
carries it to `R(τ_k)`. The order is `reach`'s own, `reachOrder_admissible`'s.
-/

-- Authors:       Tobias Ladner
-- Written:       24-September-2026
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


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every `t ∈ [0, tFinal]` is in a window `[k Δt, k Δt + Δt]` that `reach` keeps. -/
theorem aux_reach_window {tFinal Δt t : ℝ} (hΔt : 0 < Δt) (ht : t ∈ Set.Icc 0 tFinal) :
    ∃ k < max 1 ⌈tFinal / Δt⌉₊, (k : ℝ) * Δt ≤ t ∧ t - k * Δt ≤ Δt := by -- --- PROOF ---
  -- `k = c - 1`, the window whose right end `c Δt` is the first to reach `t`
  obtain ⟨c, hc⟩ : ∃ c, c = ⌈t / Δt⌉₊ := ⟨_, rfl⟩
  have hq : 0 ≤ t / Δt := div_nonneg ht.1 hΔt.le
  have hcN : c ≤ ⌈tFinal / Δt⌉₊ := hc ▸ Nat.ceil_mono (div_le_div_of_nonneg_right ht.2 hΔt.le)
  have hup : t ≤ c * Δt := (div_le_iff₀ hΔt).mp (hc ▸ Nat.le_ceil _)
  refine ⟨c - 1, by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos c with h0 | hpos
    · simp [h0, ht.1]
    · have hlt : (c : ℝ) < t / Δt + 1 := hc ▸ Nat.ceil_lt_add_one hq
      rw [Nat.cast_sub hpos, Nat.cast_one, ← le_div_iff₀ hΔt]
      linarith
  · have hc1 : (c : ℝ) ≤ ((c - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : c ≤ c - 1 + 1)
    nlinarith [mul_le_mul_of_nonneg_right hc1 hΔt.le]


-- =======================================  MAIN THEOREM  ======================================= --

/-- Every image of the initial set under the flow, at every `t ∈ [0, tFinal]`,
is in one of `reach`'s windows. -/
theorem LinearSys.reach_outer (sys : LinearSys 𝕋 n) {tFinal Δt : ℝ} {η : ℕ} (hΔt : 0 < Δt)
    (X₀ : S n) : sys.reachExact tFinal (construct X₀)
      ⊆ construct (sys.reach tFinal Δt η X₀) := by -- --- PROOF ---
  rintro _ ⟨t, ht, x₀, hx₀, rfl⟩
  obtain ⟨k, hk, hkt, htk⟩ := aux_reach_window hΔt ht
  -- the order `reach` runs at, `m + 2` in `timeIntervalStep_outer`'s naming
  obtain ⟨m, hm⟩ : ∃ m, max η (sys.reachOrder Δt + 2) = m + 2 :=
    ⟨max η (sys.reachOrder Δt + 2) - 2, by omega⟩
  have hε : ‖Δt • toRealMat sys.A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1 :=
    sys.reachOrder_admissible Δt (hm ▸ le_max_right _ _)
  -- `τ = t - t_k ∈ [0, Δt]`, so `R(τ_0)` holds `e^{Aτ} x₀`
  have hτ := sys.timeIntervalStep_outer hΔt hε X₀ (sub_nonneg.mpr hkt) htk
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
  -- window `k` is `e^{A t_k} R(τ_0)`, and `k < N`
  refine SetUnion.mem_construct.mpr ⟨sys.reachStepk Δt (m + 2) X₀ k, ?_, ?_⟩
  · rw [← hm]
    exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  · rw [hexp]
    exact Mtimes.mtimes_outer _ _ (Set.mem_biUnion rfl (Set.mem_image_of_mem _ hτ))

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
