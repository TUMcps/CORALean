import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The propagator's norm, unconditionally

`‖e^{tA}‖ ≤ e^{t‖A‖}`, which is what bounds a horizon's worth of propagators by
one constant. The matrix series is dominated termwise by the real exponential's
own, exactly as `norm_exp_sub_expTaylor_le` is, but with no side condition at
all: nothing is truncated, so no geometric tail has to converge.

The zeroth term is the one that is not `norm_pow_le'`: `‖A⁰‖` is the identity's
own `l∞` operator norm, which is at most `1` — exactly `1` except in dimension
`0`, where the supremum defining it is over an empty index set.
-/

-- Authors:       Claude Opus 5
-- Written:       18-September-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The identity is a diagonal matrix, so its norm is that of its diagonal. -/
theorem aux_norm_one_le : ‖(1 : Mat ℝ n n)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.linfty_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by simp

/-- Every power is submultiplicative, the zeroth one by the identity's norm. -/
theorem aux_norm_pow_le (x : Mat ℝ n n) (i : ℕ) : ‖x ^ i‖ ≤ ‖x‖ ^ i := by
  cases i with
  | zero => simpa using aux_norm_one_le (n := n)
  | succ k => exact norm_pow_le' x (Nat.succ_pos k)

/-- The matrix exponential's series against the real exponential's, term by
term. -/
theorem aux_norm_exp_le (x : Mat ℝ n n) : ‖exp x‖ ≤ Real.exp ‖x‖ := by -- --- PROOF ---
  set f : ℕ → Mat ℝ n n := fun i => ((Nat.factorial i : ℝ)⁻¹) • x ^ i with hf
  set g : ℕ → ℝ := fun i => ((Nat.factorial i : ℝ)⁻¹) • ‖x‖ ^ i with hg
  have hnorm : Summable (fun i => ‖f i‖) := norm_expSeries_summable' (𝕂 := ℝ) x
  have hgsum : Summable g := expSeries_summable' (𝕂 := ℝ) ‖x‖
  have hx : exp x = ∑' i : ℕ, f i := by rw [exp_eq_tsum (𝕂 := ℝ)]
  -- the real exponential as the same series at `‖x‖`
  have hRealExp : Real.exp ‖x‖ = ∑' i : ℕ, g i := by
    have h : Real.exp = fun y : ℝ => ∑' i : ℕ, ((Nat.factorial i : ℝ)⁻¹) • y ^ i := by
      rw [Real.exp_eq_exp_ℝ]; exact exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)
    rw [h]
  rw [hx, hRealExp]
  refine le_trans (norm_tsum_le_tsum_norm hnorm) (Summable.tsum_le_tsum ?_ hnorm hgsum)
  intro i
  rw [hf, hg]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤
    ((Nat.factorial i : ℝ))⁻¹), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (aux_norm_pow_le x i) (by positivity)


-- =======================================  MAIN THEOREM  ======================================= --

/-- `e^{tA}` never grows faster than the real exponential at `t‖A‖`. -/
theorem MatExp.norm_exp_smul_le (A : Mat ℝ n n) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • A)‖ ≤ Real.exp (t * ‖A‖) := by
  have h1 : ‖exp (t • A)‖ ≤ Real.exp ‖t • A‖ := aux_norm_exp_le (t • A)
  have h2 : ‖t • A‖ = t * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  rwa [h2] at h1

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
