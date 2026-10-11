import CORALean.ContDynamics.LinearSys.Krylov.Theorems.InputSolutionMemBox
import CORALean.ContDynamics.LinearSys.Theorems.ExpIntegralMulVec
import CORALean.ContDynamics.LinearSys.Theorems.MulVecL
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The input solution over a part of the step, corrected

[1, Cor. IV.1] writes `∫_{t₀}^{tₑ} e^{A(δ-t)}dt u` as the difference of `Lemma IV.1` at `δ - t₀`
and at `δ - tₑ`, and so as `P Ṽ (e^{H̃(δ-t₀)} - e^{H̃(δ-tₑ)}) e₁` plus an error. The two errors are
two boxes, of radii `ε̃(δ - t₀)` and `ε̃(δ - tₑ)`, and their difference has the sum of the radii,
`ε̃((δ - t₀) + (δ - tₑ))`; [1] prints `ε̃(tₑ - t₀)`, which fails
(`partial_input_solution_counterexample`). This is the corrected statement, from (3) on
`[0, δ]`, the hypothesis of `Lemma IV.1`. The proof of [1, Thm. IV.2] (Appendix A) sums the
printed statement over `l` sub-intervals of `[0, δ]`; with these radii the sum grows with `l`.

## References

* [1] M. Althoff. "Reachability Analysis of Large Linear Systems with Uncertain Inputs in the
  Krylov Subspace". IEEE Transactions on Automatic Control, 65(2):477-492, 2020.
-/

-- Authors:       Tobias Ladner
-- Written:       11-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n m : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `∫_{t₀}^{tₑ} e^{A(δ-t)}dt u = (∫₀^{δ-t₀} - ∫₀^{δ-tₑ}) e^{At}dt u`, the first line of [1]'s
proof. -/
theorem Krylov.aux_integral_eq_sub (A : Mat ℝ n n) (u : Vec ℝ n) {δ t₀ tₑ : ℝ}
    (h0 : t₀ ≤ δ) (he : tₑ ≤ δ) :
    (∫ t in t₀..tₑ, exp ((δ - t) • A) *ᵥ u)
      = MatExp.expIntegral A (δ - t₀) *ᵥ u
        - MatExp.expIntegral A (δ - tₑ) *ᵥ u := by -- --- PROOF ---
  have hcont : Continuous fun σ : ℝ => exp (σ • A) *ᵥ u :=
    (mulVecL.continuous.comp (exp_continuous.comp (continuous_id.smul continuous_const))).clm_apply
      continuous_const
  rw [intervalIntegral.integral_comp_sub_left (fun σ : ℝ => exp (σ • A) *ᵥ u) δ,
    Real.MatExp.expIntegral_mulVec A u (sub_nonneg.2 h0),
    Real.MatExp.expIntegral_mulVec A u (sub_nonneg.2 he),
    intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]


-- =======================================  MAIN THEOREM  ======================================= --

/-- [1, Cor. IV.1], corrected: the error box has radius `ε̃((δ - t₀) + (δ - tₑ))`. -/
theorem Krylov.partialInputSolution_mem_box (A : Mat ℝ n n) (u : Vec ℝ n)
    (V : Mat ℝ (n + 1) m) (H : Mat ℝ m m) (e₁ : Vec ℝ m) {ε δ t₀ tₑ : ℝ}
    (ht₀ : 0 ≤ t₀) (htₑ : t₀ ≤ tₑ) (hδ : tₑ ≤ δ)
    (h3 : ∀ s ∈ Set.Icc 0 δ,
      ‖exp (s • Krylov.augment A u) *ᵥ (Pi.single (Fin.last n) 1 : Fin (n + 1) → ℝ)
        - V *ᵥ (exp (s • H) *ᵥ e₁)‖₂ ≤ ε * s) :
    ∃ r : Vec ℝ n, (∀ j, |r j| ≤ ε * ((δ - t₀) + (δ - tₑ))) ∧
      (∫ t in t₀..tₑ, exp ((δ - t) • A) *ᵥ u)
        = (fun j => (V *ᵥ ((exp ((δ - t₀) • H) - exp ((δ - tₑ) • H)) *ᵥ e₁)) (Fin.castSucc j))
          + r := by -- --- PROOF ---
  -- `Lemma IV.1` at both ends of `[δ - tₑ, δ - t₀] ⊆ [0, δ]`
  obtain ⟨r₁, hr₁, h₁⟩ := Krylov.inputSolution_mem_box A u V H e₁
    (h3 (δ - t₀) ⟨by linarith, by linarith⟩)
  obtain ⟨r₂, hr₂, h₂⟩ := Krylov.inputSolution_mem_box A u V H e₁
    (h3 (δ - tₑ) ⟨by linarith, by linarith⟩)
  refine ⟨r₁ - r₂, fun j => ?_, ?_⟩
  · -- the two boxes subtract to the sum of their radii
    rw [Pi.sub_apply, mul_add]
    exact (abs_sub _ _).trans (add_le_add (hr₁ j) (hr₂ j))
  · rw [Krylov.aux_integral_eq_sub A u (by linarith) hδ, h₁, h₂, sub_mulVec, mulVec_sub]
    funext j
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
