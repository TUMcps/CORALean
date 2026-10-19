module

public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionInnerConverges
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionInnerSubsetInputSolutionSet
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionSetDistInner

@[expose] public section

/-!
# The outer approximation converges to the exact particular solution

The outer half of [1, Prop. 1], with a rate. Both directions of the distance are
measured through the *inner* approximation, which is what the proposition's own
proof does: the inner set is inside both the exact solution and the outer one,
one step of the outer set is `O(Δt²)` from it, and one step of the exact
solution is too, so neither direction needs an upper bound on a set that a
representation would only over-approximate.

`Δt‖A‖ ≤ 1` is the one-step estimate's hypothesis and also gives the truncation
order's side condition; the enclosure `Z_S ⊆ Ẑ_S` is never used, and so no
convexity is asked of the outer approximation's interval-matrix factor.

## References

* [1] M. Wetzlinger and M. Althoff. "Backward Reachability Analysis of Perturbed
      Continuous-Time Linear Systems Using Set Propagation". IEEE Transactions on
      Automatic Control, 71(1):352-367, 2026.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean

open CORALean.Real
open Matrix ContSet Scalar NormedSpace Pointwise

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {𝕋 : Type} [Scalar 𝕋]
variable {S : ℕ → Type} [∀ n, ContSet (S n) (Vec ℝ n)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Prop. 1], outer half: the Hausdorff distance to the exact particular
solution over `t = ωΔt` is `O(Δt)`, hence `0` in the limit. -/
theorem LinearSys.hausdorffDist₂_inputSolutionSet_le (sys : LinearSys 𝕋 n) {U : S n}
    {Δt ρ : ℝ} (hΔt : 0 < Δt) (hAΔ : Δt * ‖toRealMat sys.A‖ ≤ 1)
    (hconv : Convex ℝ (construct U)) (hclosed : IsClosed (construct U))
    (hbdd : Bornology.IsBounded (construct U)) (hne : (construct U).Nonempty)
    (hρ : ∀ v ∈ construct U, ‖v‖ ≤ ρ) (η : ℕ) (ω : ℕ) : -- --- CONCL ---
    hausdorffDist₂ (sys.propagateInputSolution Δt (sys.inputSolutionSet U Δt η) ω)
        (sys.inputReach U ((ω : ℝ) * Δt))
      ≤ Real.sqrt n * (ρ * ‖toRealMat sys.A‖
          * (2 * (n : ℝ) + 2 + 3 * Real.exp (Δt * ‖toRealMat sys.A‖))
          * Real.exp (((ω : ℝ) * Δt) * ‖toRealMat sys.A‖)
          * ((ω : ℝ) * Δt) * Δt) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  obtain ⟨v₀, hv₀⟩ := hne
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ _ hv₀)
  have hnorm : ‖Δt • A‖ = Δt * ‖A‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hΔt.le]
  have hε : ‖Δt • A‖ / ((η : ℝ) + 2) < 1 := by
    rw [hnorm, div_lt_one (by positivity)]
    have : (0:ℝ) ≤ (η : ℝ) := Nat.cast_nonneg η
    linarith
  set c := ρ * ‖A‖ * (2 * (n : ℝ) + 2 + 3 * Real.exp (Δt * ‖A‖)) * Δt ^ 2 with hc
  set M := Real.exp (((ω : ℝ) * Δt) * ‖A‖) with hM
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg (mul_nonneg hρ0 (norm_nonneg _))
      (by positivity)) (sq_nonneg _)
  have hbnd : 0 ≤ (ω : ℝ) * (M * c) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_nonneg _) hc0)
  have hprod : ρ * ‖A‖ * (2 * (n : ℝ) + 2 + 3 * Real.exp (Δt * ‖A‖)) * M * ((ω : ℝ) * Δt) * Δt
      = (ω : ℝ) * (M * c) := by rw [hc]; ring
  -- the propagator's norm over the horizon, which is what `M` is
  have hexpM : ∀ k : ℕ, k < ω → ‖exp (((k : ℝ) * Δt) • A)‖ ≤ M := by
    intro k hk
    rw [hM]
    refine le_trans (MatExp.norm_exp_smul_le A (mul_nonneg (Nat.cast_nonneg k) hΔt.le)) ?_
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.le) hΔt.le) (norm_nonneg _))
  -- the inner set, inside both the exact solution and the outer one
  have hstep := sys.propagateInputSolution_inputReach (U := U) hΔt.le hbdd ⟨v₀, hv₀⟩ ω
  have hinExact : sys.propagateInputSolution Δt (sys.inputSolutionInner U Δt) ω
      ⊆ sys.inputReach U ((ω : ℝ) * Δt) := by
    rw [← hstep]
    exact sys.propagateInputSolution_mono Δt
      (sys.inputSolutionInner_subset_inputReach hΔt.le) ω
  have hinOuter : sys.propagateInputSolution Δt (sys.inputSolutionInner U Δt) ω
      ⊆ sys.propagateInputSolution Δt (sys.inputSolutionSet U Δt η) ω :=
    sys.propagateInputSolution_mono Δt
      (sys.inputSolutionInner_subset_inputSolutionSet hΔt.le η hε) ω
  rw [hprod]
  refine hausdorffDist₂_le_of_mem_dist (mul_nonneg (Real.sqrt_nonneg _) hbnd) ?_ ?_
  · -- from the outer set: one step is `O(Δt²)` from the inner one, which is exact
    intro x hx
    obtain ⟨y, hy, hxy⟩ := sys.propagateInputSolution_dist Δt (M := M) (c := c)
      (Real.exp_nonneg _)
      (fun z hz => by
        obtain ⟨v, hv, hzv⟩ :=
          sys.inputSolutionSet_dist_inputSolutionInner hΔt hAΔ ⟨v₀, hv₀⟩ hρ η z hz
        refine ⟨v, hv, le_trans hzv ?_⟩
        rw [hc]
        have := Real.exp_pos (Δt * ‖A‖)
        nlinarith [mul_nonneg hρ0 (norm_nonneg A), sq_nonneg Δt,
          mul_nonneg (mul_nonneg hρ0 (norm_nonneg A)) (sq_nonneg Δt)])
      ω hexpM x hx
    exact ⟨y, hinExact hy, le_trans (norm₂_le_sqrt_mul_norm _)
      (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _))⟩
  · -- from the exact solution: the same one-step estimate, then into the outer set
    intro x hx
    rw [← hstep] at hx
    obtain ⟨y, hy, hxy⟩ := sys.propagateInputSolution_dist Δt (M := M) (c := c)
      (Real.exp_nonneg _)
      (fun z hz => by
        obtain ⟨v, hv, hzv⟩ :=
          sys.inputReach_dist_inputSolutionInner hΔt hconv hclosed hbdd hρ z hz
        refine ⟨v, hv, le_trans hzv ?_⟩
        rw [hc]
        have := Real.exp_pos (Δt * ‖A‖)
        nlinarith [mul_nonneg hρ0 (norm_nonneg A), sq_nonneg Δt,
          mul_nonneg (mul_nonneg hρ0 (norm_nonneg A)) (sq_nonneg Δt),
          Nat.cast_nonneg (α := ℝ) n])
      ω hexpM x hx
    exact ⟨y, hinOuter hy, le_trans (norm₂_le_sqrt_mul_norm _)
      (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
