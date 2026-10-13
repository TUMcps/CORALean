module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegral
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpTail2

@[expose] public section

/-!
# `∫₀ʳ e^{As} ds` against `r I`

`‖A‖ · ‖∫₀ʳ e^{As} ds - r I‖ ≤ e^{r‖A‖} - 1 - r‖A‖` for `r ≥ 0`: the series
`∑ᵢ r^{i+1}/(i+1)! Aⁱ` with its zeroth term `r I` taken off, compared termwise with the
exponential's tail after one more factor of `‖A‖`. Stated with `‖A‖` multiplied rather than
divided, so that `A = 0`, where both sides vanish, needs no hypothesis.

What a constant input contributes over a step, `∫₀ʳ e^{A(r-s)} u ds`, is within
`(e^{r‖A‖} - 1 - r‖A‖)/‖A‖ · ‖u‖` of `r u`: the first of the two terms the proof of
[1, Lemma 1] bounds.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Claude Opus 5.5
-- Written:       01-October-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- =======================================  MAIN THEOREM  ======================================= --

/-- `∫₀ʳ e^{As} ds` is `r I` up to the exponential's second-order remainder, over `‖A‖`. -/
theorem MatExp.norm_mul_norm_expIntegral_sub_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 ≤ r) :
    ‖A‖ * ‖MatExp.expIntegral A r - r • (1 : Mat ℝ n n)‖
      ≤ Real.exp (r * ‖A‖) - 1 - r * ‖A‖ := by -- --- PROOF ---
  rcases (norm_nonneg A).eq_or_lt with hA | hA
  · rw [← hA]; simp
  -- the series with its zeroth term, `r I`, taken off
  have hsum : HasSum (fun i : ℕ => (((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i)
      (MatExp.expIntegral A r) := (MatExp.summable_expIntegral A r).hasSum
  have htail : HasSum
      (fun i : ℕ => (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2)) • A ^ (i + 1))
      (MatExp.expIntegral A r - r • (1 : Mat ℝ n n)) := by
    have := (hasSum_nat_add_iff' 1).mpr hsum
    have heq : MatExp.expIntegral A r - ∑ i ∈ Finset.range 1,
        (((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i
          = MatExp.expIntegral A r - r • (1 : Mat ℝ n n) := by
      simp
    rwa [heq] at this
  -- termwise, each order one factor of `‖A‖` short of the exponential's tail
  have hg : HasSum (fun i : ℕ => (r * ‖A‖) ^ (i + 2) / ((i + 2).factorial : ℝ) / ‖A‖)
      ((Real.exp (r * ‖A‖) - 1 - r * ‖A‖) / ‖A‖) := (hasSum_exp_tail2 _).div_const _
  have hle := htail.norm_le_of_bounded hg fun i => by
    rw [norm_smul, Real.norm_eq_abs]
    have hfac : (0:ℝ) < ((i + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpow : ‖A ^ (i + 1)‖ ≤ ‖A‖ ^ (i + 1) := norm_pow_le' A (by omega)
    rw [abs_of_nonneg (mul_nonneg (inv_pos.mpr hfac).le (pow_nonneg hr _))]
    calc ((i + 2).factorial : ℝ)⁻¹ * r ^ (i + 2) * ‖A ^ (i + 1)‖
        ≤ ((i + 2).factorial : ℝ)⁻¹ * r ^ (i + 2) * ‖A‖ ^ (i + 1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (inv_pos.mpr hfac).le (pow_nonneg hr _))
      _ = (r * ‖A‖) ^ (i + 2) / ((i + 2).factorial : ℝ) / ‖A‖ := by
          field_simp
          ring
  calc ‖A‖ * ‖MatExp.expIntegral A r - r • (1 : Mat ℝ n n)‖
      ≤ ‖A‖ * ((Real.exp (r * ‖A‖) - 1 - r * ‖A‖) / ‖A‖) := mul_le_mul_of_nonneg_left hle hA.le
    _ = Real.exp (r * ‖A‖) - 1 - r * ‖A‖ := by field_simp

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
