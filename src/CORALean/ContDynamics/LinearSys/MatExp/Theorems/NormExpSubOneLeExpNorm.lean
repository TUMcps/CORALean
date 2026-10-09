import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# `exp x` stays within `Real.exp ‖x‖ - 1` of the identity

The series of `exp x - 1` compared termwise with that of `Real.exp ‖x‖ - 1`, under the `l∞`
operator norm, with no side condition on `‖x‖`. `norm_exp_smul_sub_one_le` loosens it to
`t‖A‖e^{t‖A‖}`; the float step error `timeIntervalStepErrorFloat` uses it as it stands.
-/

-- Authors:       Tobias Ladner
-- Written:       18-September-2026
-- Last update:   08-October-2026
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- One term of `exp x - 1`'s tail, bounded by the matching term of
`Real.exp ‖x‖ - 1`. -/
theorem aux_norm_exp_tail_term_le (x : Mat ℝ n n) (i : ℕ) :
    ‖(((Nat.factorial (i + 1) : ℝ))⁻¹) • x ^ (i + 1)‖
      ≤ ((Nat.factorial (i + 1) : ℝ))⁻¹ * ‖x‖ ^ (i + 1) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos i)) (by positivity)


-- =======================================  MAIN THEOREM  ======================================= --

-- the `Real.exp_eq_exp_ℝ` rewrite against the four local matrix instances is what is slow
set_option maxHeartbeats 400000 in
/-- `exp x` sits at most `Real.exp ‖x‖ - 1` away from the identity: the matrix
series is dominated termwise by the real exponential's own. -/
theorem norm_exp_sub_one_le_exp_norm (x : Mat ℝ n n) :
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

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
