import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpSmulTsum
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpSmul
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpTail2

/-!
# The flow against the straight line between the ends of a step

[1, Lemma 2]'s eq. 6: for `0 ≤ t ≤ r`, the homogeneous solution `e^{tA}z` is within
`(e^{r‖A‖} - 1 - r‖A‖)‖z‖` of the point `z + (t/r)(e^{rA}z - z)` on the segment from `z` to
`e^{rA}z`. Term by term, as the printed proof has it: the difference is
`∑_{k≥2} (t^k - t r^{k-1})/k! · A^k z`, the constant and linear orders cancelling, and
`|t^k - t r^{k-1}| ≤ r^k` on `[0, r]`.

At `r = 0` the window is the point `t = 0`, where both sides vanish; `t / r` is then
Lean's `0 / 0 = 0`, which is harmless there.

## References

* [1] A. Girard. "Reachability of Uncertain Linear Systems Using Zonotopes". In Hybrid
      Systems: Computation and Control (HSCC), LNCS 3414, Springer, 2005, pp. 291-305.
-/

-- Authors:       Tobias Ladner
-- Written:       01-October-2026
-- Last update:   ---
-- Last revision: ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Both `t^k` and `t r^{k-1}` lie in `[0, r^k]`, so they differ by at most `r^k`. -/
theorem aux_abs_pow_sub_div_mul_pow_le {t r : ℝ} (ht : 0 ≤ t) (htr : t ≤ r) (k : ℕ) :
    |t ^ k - t / r * r ^ k| ≤ r ^ k := by -- --- PROOF ---
  have hr : 0 ≤ r := ht.trans htr
  have h1 : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : t ^ k ≤ r ^ k := pow_le_pow_left₀ ht htr k
  have h3 : 0 ≤ t / r * r ^ k := by positivity
  have h4 : t / r * r ^ k ≤ r ^ k := by
    rcases hr.eq_or_lt with h | h
    · subst h; simp
    · calc t / r * r ^ k ≤ 1 * r ^ k := by gcongr; exact (div_le_one h).mpr htr
        _ = r ^ k := one_mul _
  exact abs_sub_le_of_nonneg_of_le h1 h2 h3 h4


-- =======================================  MAIN THEOREM  ======================================= --

-- `tsum` and `HasSum` over the matrix algebra, under the four local `linftyOp*` instances
set_option maxHeartbeats 400000 in
/-- [1, Lemma 2], eq. 6: `e^{tA}z` against the segment from `z` to `e^{rA}z`. -/
theorem MatExp.norm_exp_mulVec_sub_interpolate_le (A : Mat ℝ n n) {t r : ℝ} (ht : 0 ≤ t)
    (htr : t ≤ r) (z : Vec ℝ n) :
    ‖exp (t • A) *ᵥ z - z - (t / r) • (exp (r • A) *ᵥ z - z)‖
      ≤ (Real.exp (r * ‖A‖) - 1 - r * ‖A‖) * ‖z‖ := by -- --- PROOF ---
  set M : Mat ℝ n n := exp (t • A) - 1 - (t / r) • (exp (r • A) - 1) with hMdef
  have hM : exp (t • A) *ᵥ z - z - (t / r) • (exp (r • A) *ᵥ z - z) = M *ᵥ z := by
    simp only [hMdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hM]
  refine (Matrix.linfty_opNorm_mulVec M z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg z))
  -- both exponentials as one series in the powers of `A`
  have hsum : ∀ σ : ℝ, HasSum (fun i : ℕ => (((i.factorial : ℝ))⁻¹ * σ ^ i) • A ^ i)
      (exp (σ • A)) := fun σ => by
    rw [exp_smul_tsum]; exact (summable_exp_smul A σ).hasSum
  set d : ℕ → ℝ := fun i =>
    ((i.factorial : ℝ))⁻¹ * t ^ i - t / r * (((i.factorial : ℝ))⁻¹ * r ^ i) with hddef
  have hd : HasSum (fun i : ℕ => d i • A ^ i) (exp (t • A) - (t / r) • exp (r • A)) := by
    refine ((hsum t).sub ((hsum r).const_smul (t / r))).congr_fun fun i => ?_
    simp only [hddef, sub_smul, smul_smul]
  -- the linear order cancels, and the constant one is what `M` subtracts
  have hd1 : d 1 = 0 := by
    simp only [hddef, Nat.factorial_one, Nat.cast_one, inv_one, one_mul, pow_one]
    rcases (ht.trans htr).eq_or_lt with h | h
    · subst h
      have : t = 0 := le_antisymm htr ht
      subst this; simp
    · field_simp; ring
  have htail : HasSum (fun i : ℕ => d (i + 2) • A ^ (i + 2)) M := by
    have := (hasSum_nat_add_iff' 2).mpr hd
    have hd0 : d 0 = 1 - t / r := by simp [hddef]
    have heq : exp (t • A) - (t / r) • exp (r • A) - ∑ i ∈ Finset.range 2, d i • A ^ i = M := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, hd1, zero_smul,
        add_zero, zero_add, pow_zero, hMdef, hd0, smul_sub, sub_smul, one_smul]
      abel
    rwa [heq] at this
  -- termwise against the tail of `e^{r‖A‖}`
  refine htail.norm_le_of_bounded (hasSum_exp_tail2 (r * ‖A‖)) fun i => ?_
  rw [norm_smul, Real.norm_eq_abs]
  have hpow : ‖A ^ (i + 2)‖ ≤ ‖A‖ ^ (i + 2) := norm_pow_le' A (by omega)
  have hfac : (0:ℝ) < ((i + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcoef : |d (i + 2)| ≤ r ^ (i + 2) / ((i + 2).factorial : ℝ) := by
    have : d (i + 2) = ((i + 2).factorial : ℝ)⁻¹ * (t ^ (i + 2) - t / r * r ^ (i + 2)) := by
      simp only [hddef]; ring
    rw [this, abs_mul, abs_of_pos (inv_pos.mpr hfac)]
    calc ((i + 2).factorial : ℝ)⁻¹ * |t ^ (i + 2) - t / r * r ^ (i + 2)|
        ≤ ((i + 2).factorial : ℝ)⁻¹ * r ^ (i + 2) :=
          mul_le_mul_of_nonneg_left (aux_abs_pow_sub_div_mul_pow_le ht htr _)
            (inv_pos.mpr hfac).le
      _ = r ^ (i + 2) / ((i + 2).factorial : ℝ) := by rw [div_eq_inv_mul]
  calc |d (i + 2)| * ‖A ^ (i + 2)‖ ≤ r ^ (i + 2) / ((i + 2).factorial : ℝ) * ‖A‖ ^ (i + 2) :=
        mul_le_mul hcoef hpow (norm_nonneg _) (div_nonneg (pow_nonneg (ht.trans htr) _) hfac.le)
    _ = (r * ‖A‖) ^ (i + 2) / ((i + 2).factorial : ℝ) := by rw [mul_pow]; ring

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
