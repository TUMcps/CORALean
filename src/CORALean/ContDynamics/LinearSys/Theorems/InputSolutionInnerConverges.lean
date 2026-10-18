module

public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.NormExpSmulLe
public import CORALean.ContDynamics.LinearSys.Theorems.InputReachDistInner
public import CORALean.ContDynamics.LinearSys.Theorems.InputSolutionInnerSubsetInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputReach
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionDist
public import CORALean.ContDynamics.LinearSys.Theorems.PropagateInputSolutionMono
public import CORALean.Global.EuclideanHausdorffDist

@[expose] public section

/-!
# The inner approximation converges to the exact particular solution

The inner half of [1, Prop. 1], with a rate rather than only the limit: the
Hausdorff distance over the horizon `t = ωΔt` is at most a constant times `Δt`.
One step costs `O(Δt²)` by `inputReach_dist_inputSolutionInner`, the `ω = t/Δt`
steps carry it at a factor `e^{‖A‖t}` each, and the propagation is exact on the
exact particular solution, so the two sets being compared are nested and only
one side of the distance has anything to prove.

`√n` converts the supremum norm `Vec ℝ n` carries into the `‖·‖₂` the paper
measures its Hausdorff distance in; the `Δt` inside the exponential is what the
one-step estimate contributes and vanishes with it.

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

/-- [1, Prop. 1], inner half: the Hausdorff distance to the exact particular
solution over `t = ωΔt` is `O(Δt)`, hence `0` in the limit. -/
theorem LinearSys.hausdorffDist₂_inputSolutionInner_le (sys : LinearSys 𝕋 n) {U : S n}
    {Δt ρ : ℝ} (hΔt : 0 < Δt) (hconv : Convex ℝ (construct U))
    (hclosed : IsClosed (construct U)) (hbdd : Bornology.IsBounded (construct U))
    (hne : (construct U).Nonempty) (hρ : ∀ v ∈ construct U, ‖v‖ ≤ ρ) (ω : ℕ) : -- --- STMT ---
    hausdorffDist₂ (sys.propagateInputSolution Δt (sys.inputSolutionInner U Δt) ω)
        (sys.inputReach U ((ω : ℝ) * Δt))
      ≤ Real.sqrt n * (2 * ρ * ‖toRealMat sys.A‖
          * Real.exp (((ω : ℝ) * Δt + Δt) * ‖toRealMat sys.A‖)
          * ((ω : ℝ) * Δt) * Δt) := by -- --- PROOF ---
  set A := toRealMat sys.A with hA
  obtain ⟨v₀, hv₀⟩ := hne
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (hρ _ hv₀)
  set c := 2 * ρ * ‖A‖ * Real.exp (Δt * ‖A‖) * Δt ^ 2 with hc
  set M := Real.exp (((ω : ℝ) * Δt) * ‖A‖) with hM
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (norm_nonneg _))
      (Real.exp_nonneg _)) (sq_nonneg _)
  have hbnd : 0 ≤ (ω : ℝ) * (M * c) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_nonneg _) hc0)
  -- the two constants multiply out to the one the statement names
  have hprod : 2 * ρ * ‖A‖ * Real.exp (((ω : ℝ) * Δt + Δt) * ‖A‖) * ((ω : ℝ) * Δt) * Δt
      = (ω : ℝ) * (M * c) := by
    have hexp : Real.exp (((ω : ℝ) * Δt + Δt) * ‖A‖)
        = Real.exp (((ω : ℝ) * Δt) * ‖A‖) * Real.exp (Δt * ‖A‖) := by
      rw [← Real.exp_add]; ring_nf
    rw [hM, hc, hexp]; ring
  -- the propagation is exact on the exact solution, and the inner set is inside it
  have hstep := sys.propagateInputSolution_inputReach (U := U) hΔt.le hbdd ⟨v₀, hv₀⟩ ω
  have hsub : sys.propagateInputSolution Δt (sys.inputSolutionInner U Δt) ω
      ⊆ sys.inputReach U ((ω : ℝ) * Δt) := by
    rw [← hstep]
    exact sys.propagateInputSolution_mono Δt
      (sys.inputSolutionInner_subset_inputReach hΔt.le) ω
  rw [hprod]
  refine hausdorffDist₂_le_of_mem_dist (mul_nonneg (Real.sqrt_nonneg _) hbnd) ?_ ?_
  · -- one direction is the inclusion, at distance zero
    intro x hx
    refine ⟨x, hsub hx, ?_⟩
    simp only [sub_self, norm₂_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) hbnd
  · -- the other is the one-step estimate, summed over the horizon
    intro x hx
    rw [← hstep] at hx
    obtain ⟨y, hy, hxy⟩ := sys.propagateInputSolution_dist Δt (M := M) (c := c)
      (Real.exp_nonneg _)
      (sys.inputReach_dist_inputSolutionInner hΔt hconv hclosed hbdd hρ) ω
      (fun k hk => by
        rw [hM]
        refine le_trans (MatExp.norm_exp_smul_le A (mul_nonneg (Nat.cast_nonneg k) hΔt.le)) ?_
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.le) hΔt.le) (norm_nonneg _))) x hx
    exact ⟨y, hy, le_trans (norm₂_le_sqrt_mul_norm _)
      (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _))⟩

end CORALean


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
