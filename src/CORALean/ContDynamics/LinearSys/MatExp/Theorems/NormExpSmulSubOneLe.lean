import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# `e^{tA}` stays within `t‖A‖e^{t‖A‖}` of the identity

An unconditional bound, unlike `norm_exp_sub_expTaylor_le`'s geometric-series
estimate: comparing `exp (t • A) - 1`'s own series termwise against
`Real.exp ‖t • A‖ - 1` costs nothing extra, and `e^x - 1 ≤ x e^x` for `x ≥ 0`
closes it without any `‖t • A‖ < c` side condition. This is the bound
[1, Lemma 2]'s Appendix B needs a Lipschitz constant for `e^{AΔt}` from, over
the whole of `Δt ∈ [0, t_end]` and not only a neighbourhood of `0`.

## References

* [1] M. Wetzlinger, A. Kulmburg, A. Le Penven and M. Althoff. "Adaptive
      Reachability Algorithms for Nonlinear Systems Using Abstraction Error
      Analysis". Nonlinear Analysis: Hybrid Systems, vol. 46, 2022, p. 101252.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- `e^x - 1 ≤ x e^x` for every real `x`, read off `1 - x ≤ e^{-x}` multiplied by `e^x`. -/
theorem aux_real_exp_sub_one_le_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by -- --- PROOF ---
  have h1 : 1 + (-x) ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg x)
    linarith
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_sub, mul_one] at h2
  linarith

/-- One term of `exp x - 1`'s tail, bounded by the matching term of
`Real.exp ‖x‖ - 1`. -/
theorem aux_norm_exp_tail_term_le (x : Mat ℝ n n) (i : ℕ) :
    ‖(((Nat.factorial (i + 1) : ℝ))⁻¹) • x ^ (i + 1)‖
      ≤ ((Nat.factorial (i + 1) : ℝ))⁻¹ * ‖x‖ ^ (i + 1) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos i)) (by positivity)

-- the `Real.exp_eq_exp_ℝ` rewrite against the four local matrix instances is what is slow
set_option maxHeartbeats 400000 in
/-- `exp x` sits at most `Real.exp ‖x‖ - 1` away from the identity: the matrix
series is dominated termwise by the real exponential's own. -/
theorem aux_norm_exp_sub_one_le (x : Mat ℝ n n) :
    ‖exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by -- --- PROOF ---
  -- `exp x`'s own series, and its `i = 0` term split off
  set f : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹) • x ^ i with hf
  have hsum : Summable f := expSeries_summable' (𝕂 := ℝ) x
  have hnorm : Summable (fun i => ‖f i‖) := norm_expSeries_summable' (𝕂 := ℝ) x
  have hx : exp x = ∑' i : ℕ, f i := by rw [exp_eq_tsum (𝕂 := ℝ)]
  have htail : exp x - 1 = ∑' i : ℕ, f (i + 1) := by
    rw [hx, ← hsum.sum_add_tsum_nat_add 1]
    simp [hf]
  -- the matching real series at `‖x‖`, split the same way
  set g : ℕ → ℝ := fun i => ((Nat.factorial i : ℝ)⁻¹) • ‖x‖ ^ i with hg
  have hgsum : Summable g := expSeries_summable' (𝕂 := ℝ) ‖x‖
  have hRealExp : Real.exp ‖x‖ = ∑' i : ℕ, g i := by
    have h : Real.exp = fun y : ℝ => ∑' i : ℕ, ((Nat.factorial i : ℝ)⁻¹) • y ^ i := by
      rw [Real.exp_eq_exp_ℝ]; exact exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)
    rw [h]
  have htailR : Real.exp ‖x‖ - 1 = ∑' i : ℕ, g (i + 1) := by
    rw [hRealExp, ← hgsum.sum_add_tsum_nat_add 1]
    simp [hg]
  -- the norm of the matrix tail is under the sum of norms, then term by term
  rw [htail, htailR]
  calc ‖∑' i : ℕ, f (i + 1)‖
      ≤ ∑' i : ℕ, ‖f (i + 1)‖ :=
        norm_tsum_le_tsum_norm ((summable_nat_add_iff 1).mpr hnorm)
    _ ≤ ∑' i : ℕ, g (i + 1) :=
        Summable.tsum_le_tsum (fun i => aux_norm_exp_tail_term_le x i)
          ((summable_nat_add_iff 1).mpr hnorm) ((summable_nat_add_iff 1).mpr hgsum)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{tA}` stays within `t‖A‖e^{t‖A‖}` of the identity, for every `t ≥ 0` and
with no bound on `t‖A‖` at all. -/
theorem norm_exp_smul_sub_one_le (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A) - 1‖ ≤ t * ‖A‖ * Real.exp (t * ‖A‖) := by -- --- PROOF ---
  have h1 : ‖exp (t • A) - 1‖ ≤ Real.exp ‖t • A‖ - 1 := aux_norm_exp_sub_one_le (t • A)
  have h2 : ‖t • A‖ = t * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [h2] at h1
  have h3 := aux_real_exp_sub_one_le_mul_exp (t * ‖A‖)
  linarith

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
