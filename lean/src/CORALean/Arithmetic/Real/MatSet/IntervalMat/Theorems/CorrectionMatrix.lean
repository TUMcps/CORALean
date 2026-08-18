import CORALean.Arithmetic.Real.MatSet.IntervalMat.Theorems.CorrCoeffBound
import CORALean.Arithmetic.Real.MatSet.IntervalMat.Theorems.ExpDiff
import CORALean.Arithmetic.Real.MatSet.IntervalMat.Theorems.ExpEnclosure

/-!
# The interpolation error lies in the correction matrix

Althoff's thesis (2010), Prop. 3.1. Orders `2` through `η` are kept exactly,
each contributing the interval between `corrTerm` and zero; everything past `η`
goes into the same remainder that bounds the exponential.

Substituting `t = s·r` turns order `i` into `r^i (s^i - s)`, which `corrCoeff`
bounds exactly — so the finite part is as tight as the thesis claims.

The tail is bounded with both exponentials kept in one series. Each term carries
`|t^i - t·r^(i-1)| ≤ r^i`, so the whole tail is dominated by the same geometric
series as the exponential remainder. Bounding the two remainders separately and
adding them, as the thesis proof does, would give twice this.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Arithmetic.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- A value between `L` and `0`, scaled by anything, stays between `L * w` and `0`
on whichever side the sign puts it. -/
theorem aux_mul_mem_minmax {L u w : ℝ} (hLu : L ≤ u) (hu0 : u ≤ 0) :
    min (L * w) 0 ≤ u * w ∧ u * w ≤ max (L * w) 0 := by
  rcases le_total 0 w with hw | hw
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

/-- Rewriting one order of the interpolation error through `s = t/r`. -/
theorem aux_pow_sub_eq {t r : ℝ} (hr : 0 < r) (m : ℕ) :
    t ^ m - (t / r) * r ^ m = r ^ m * ((t / r) ^ m - (t / r)) := by
  rw [div_pow]
  field_simp

set_option maxHeartbeats 400000 in
/-- Every tail term is at most `r^m` in the scalar factor, so the tail is the
exponential's own remainder series. -/
theorem aux_norm_expDiff_tail_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    ‖∑' i : ℕ, (((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
        * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖
      ≤ IntervalMat.expRemainderBound (r • A) η := by
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hrA : ‖r • A‖ = r * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hcnn : (0:ℝ) ≤ ‖r • A‖ := norm_nonneg _
  have hε0 : (0:ℝ) ≤ ‖r • A‖ / ((η : ℝ) + 2) := by positivity
  -- each term is dominated by the exponential's own tail term
  have hterm : ∀ i : ℕ,
      ‖(((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
          * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖
        ≤ (‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
            * (‖r • A‖ / ((η : ℝ) + 2)) ^ i := by
    intro i
    set m := i + (η + 1) with hm
    have hscal : |t ^ m - (t / r) * r ^ m| ≤ r ^ m := by
      rw [aux_pow_sub_eq hr m, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ m)]
      have h1 : |(t / r) ^ m - (t / r)| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [pow_nonneg hs0 m, pow_le_one₀ hs0 hs1 (n := m)]
        · nlinarith [pow_nonneg hs0 m, pow_le_one₀ hs0 hs1 (n := m)]
      nlinarith [pow_nonneg hr.le m]
    calc ‖(((Nat.factorial m : ℝ))⁻¹ * (t ^ m - (t / r) * r ^ m)) • A ^ m‖
        = |((Nat.factorial m : ℝ))⁻¹ * (t ^ m - (t / r) * r ^ m)| * ‖A ^ m‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ((Nat.factorial m : ℝ))⁻¹ * r ^ m * ‖A‖ ^ m := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((Nat.factorial m : ℝ))⁻¹)]
          gcongr
          · exact norm_pow_le' A (by omega)
      _ = ((Nat.factorial m : ℝ))⁻¹ * ‖r • A‖ ^ m := by rw [hrA, mul_pow]; ring
      _ ≤ _ := aux_scalar_term_le hcnn η i
  have hgeo : Summable (fun i : ℕ => (‖r • A‖ / ((η : ℝ) + 2)) ^ i) :=
    summable_geometric_of_lt_one hε0 hε
  have hnorm : Summable (fun i : ℕ =>
      ‖(((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
          * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm (hgeo.mul_left _)
  calc ‖∑' i : ℕ, (((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
          * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖
      ≤ ∑' i : ℕ, ‖(((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
          * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, (‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
          * (‖r • A‖ / ((η : ℝ) + 2)) ^ i :=
        Summable.tsum_le_tsum hterm hnorm (hgeo.mul_left _)
    _ = IntervalMat.expRemainderBound (r • A) η := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε, IntervalMat.expRemainderBound]

end CORALean.Arithmetic.Real
