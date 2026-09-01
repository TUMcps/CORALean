import CORALean.MatSet.IntervalMat.Theorems.CorrectionMatrix
import CORALean.MatSet.IntervalMat.Theorems.ExpIntegral

/-!
# The constant input's interpolation error lies in `constCorrectionMatrix`

Althoff's `F̃`, the integrated counterpart of `Prop. 3.1`'s `F`. What a constant
input contributes over `[0,t]` is `∫₀ᵗ e^{Aσ}dσ` applied to it, and the straight
line from `0` to its value at `r` misses that by this much.

The series is `∑ᵢ Aⁱ (t^{i+1} - (t/r)r^{i+1})/(i+1)!`, whose `i = 0` term
cancels — one order lower than for `F`, where the constant *and* linear terms
go. Orders `1` through `η` are kept exactly, through the same `corrCoeff` bound
read at one index higher, and everything past `η` goes into `E(r)·r`.

The tail is bounded as one series, never as two remainders added: each term
carries `|t^{i+2} - t·r^{i+1}| ≤ r^{i+2}`, and pulling one factor of `r` out
leaves exactly the exponential's own tail. Splitting instead would cost a factor
of two, for the reason `CorrectionMatrix` documents.
-/

-- Authors:       Tobias Ladner
-- Written:       01-September-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

set_option maxHeartbeats 400000 in
/-- The interpolation error of the integrated exponential, as one series from
order `1` up. -/
theorem IntervalMat.expIntegralDiff_eq_tsum (A : Mat ℝ n n) (t r : ℝ) (hr : r ≠ 0) :
    IntervalMat.expIntegral A t - (t / r) • IntervalMat.expIntegral A r
      = ∑' i : ℕ, (((Nat.factorial (i + 2) : ℝ))⁻¹
          * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1) := by
  set g : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + 1) : ℝ))⁻¹ * (t ^ (i + 1) - (t / r) * r ^ (i + 1))) • A ^ i with hg
  have hst := IntervalMat.summable_expIntegral A t
  have hsr : Summable (fun i : ℕ =>
      (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i)) :=
    (IntervalMat.summable_expIntegral A r).const_smul _
  have hcongr : ∀ i : ℕ,
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * t ^ (i + 1)) • A ^ i
        - (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i) = g i := by
    intro i
    rw [hg]
    simp only [smul_smul, ← sub_smul]
    ring_nf
  have hgsum : Summable g := (hst.sub hsr).congr hcongr
  have htsum : ∑' i : ℕ, g i
      = IntervalMat.expIntegral A t - (t / r) • IntervalMat.expIntegral A r := by
    rw [IntervalMat.expIntegral, IntervalMat.expIntegral, ← tsum_const_smul'' (t / r),
      ← Summable.tsum_sub hst hsr]
    exact tsum_congr fun i => (hcongr i).symm
  have hshift := hgsum.sum_add_tsum_nat_add 1
  have hfirst : ∑ i ∈ Finset.range 1, g i = 0 := by
    have h1 : t - t / r * r = 0 := by rw [div_mul_cancel₀ t hr, sub_self]
    simp [hg, h1]
  rw [← htsum, ← hshift, hfirst, zero_add]

set_option maxHeartbeats 400000 in
/-- The same series, shifted past `η`, is summable. -/
theorem IntervalMat.summable_expIntegralDiff (A : Mat ℝ n n) (t r : ℝ) :
    Summable (fun i : ℕ => (((Nat.factorial (i + 2) : ℝ))⁻¹
      * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1)) := by
  have hst := IntervalMat.summable_expIntegral A t
  have hsr : Summable (fun i : ℕ =>
      (t / r) • ((((Nat.factorial (i + 1) : ℝ))⁻¹ * r ^ (i + 1)) • A ^ i)) :=
    (IntervalMat.summable_expIntegral A r).const_smul _
  have hg : Summable (fun i : ℕ =>
      (((Nat.factorial (i + 1) : ℝ))⁻¹ * (t ^ (i + 1) - (t / r) * r ^ (i + 1))) • A ^ i) :=
    (hst.sub hsr).congr fun i => by simp only [smul_smul, ← sub_smul]; ring_nf
  exact (summable_nat_add_iff 1).mpr hg

set_option maxHeartbeats 1000000 in
/-- Every tail term carries `r^{i+2}` in its scalar factor; pulling one `r` out
leaves the exponential's own remainder series. -/
theorem aux_norm_constTail_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    ‖∑' i : ℕ, (((Nat.factorial (i + η + 2) : ℝ))⁻¹
        * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖
      ≤ r * IntervalMat.expRemainderBound (r • A) η := by
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hrA : ‖r • A‖ = r * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hcnn : (0:ℝ) ≤ ‖r • A‖ := norm_nonneg _
  have hε0 : (0:ℝ) ≤ ‖r • A‖ / ((η : ℝ) + 2) := by positivity
  have hterm : ∀ i : ℕ,
      ‖(((Nat.factorial (i + η + 2) : ℝ))⁻¹
          * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖
        ≤ r * ((‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
            * (‖r • A‖ / ((η : ℝ) + 2)) ^ i) := by
    intro i
    have hfp : (0:ℝ) < (Nat.factorial (i + η + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hfle : (Nat.factorial (i + η + 1) : ℝ) ≤ (Nat.factorial (i + η + 2) : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hscal : |t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2)| ≤ r ^ (i + η + 2) := by
      rw [aux_pow_sub_eq hr (i + η + 2), abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (i + η + 2))]
      have h1 : |(t / r) ^ (i + η + 2) - (t / r)| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [pow_nonneg hs0 (i + η + 2), pow_le_one₀ hs0 hs1 (n := i + η + 2)]
        · nlinarith [pow_nonneg hs0 (i + η + 2), pow_le_one₀ hs0 hs1 (n := i + η + 2)]
      nlinarith [pow_nonneg hr.le (i + η + 2)]
    calc ‖(((Nat.factorial (i + η + 2) : ℝ))⁻¹
            * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖
        = |((Nat.factorial (i + η + 2) : ℝ))⁻¹
            * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))| * ‖A ^ (i + η + 1)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ((Nat.factorial (i + η + 1) : ℝ))⁻¹ * r ^ (i + η + 2) * ‖A‖ ^ (i + η + 1) := by
          rw [abs_mul,
            abs_of_nonneg (by positivity : (0:ℝ) ≤ ((Nat.factorial (i + η + 2) : ℝ))⁻¹)]
          gcongr
          · exact norm_pow_le' A (by omega)
      _ = r * (((Nat.factorial (i + η + 1) : ℝ))⁻¹ * ‖r • A‖ ^ (i + η + 1)) := by
          rw [hrA, mul_pow, pow_succ]
          ring
      _ ≤ r * ((‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
            * (‖r • A‖ / ((η : ℝ) + 2)) ^ i) := by
          refine mul_le_mul_of_nonneg_left ?_ hr.le
          have h := aux_scalar_term_le hcnn η i
          rwa [show i + (η + 1) = i + η + 1 from by omega] at h
  have hgeo : Summable (fun i : ℕ => (‖r • A‖ / ((η : ℝ) + 2)) ^ i) :=
    summable_geometric_of_lt_one hε0 hε
  have hnorm : Summable (fun i : ℕ =>
      ‖(((Nat.factorial (i + η + 2) : ℝ))⁻¹
          * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm
      ((hgeo.mul_left _).mul_left _)
  calc ‖∑' i : ℕ, (((Nat.factorial (i + η + 2) : ℝ))⁻¹
          * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖
      ≤ ∑' i : ℕ, ‖(((Nat.factorial (i + η + 2) : ℝ))⁻¹
          * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, r * ((‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
          * (‖r • A‖ / ((η : ℝ) + 2)) ^ i) :=
        Summable.tsum_le_tsum hterm hnorm ((hgeo.mul_left _).mul_left _)
    _ = r * IntervalMat.expRemainderBound (r • A) η := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hε0 hε,
          IntervalMat.expRemainderBound]

set_option maxHeartbeats 1000000 in
/-- Althoff's `F̃` contains the constant input's interpolation error, at every
time of the step. -/
theorem IntervalMat.expIntegralDiff_mem_constCorrectionMatrix (A : Mat ℝ n n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) :
    IntervalMat.expIntegral A t - (t / r) • IntervalMat.expIntegral A r
      ∈ (IntervalMat.constCorrectionMatrix A r η).construct := by
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  set f : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + 2) : ℝ))⁻¹ * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1)
    with hf
  have hsum : Summable f := IntervalMat.summable_expIntegralDiff A t r
  have hsplit := hsum.sum_add_tsum_nat_add η
  have heq : IntervalMat.expIntegral A t - (t / r) • IntervalMat.expIntegral A r
      = (∑ i ∈ Finset.range η, f i) + ∑' i : ℕ, f (i + η) := by
    rw [IntervalMat.expIntegralDiff_eq_tsum A t r hr.ne', ← hsplit]
  have htail : ‖∑' i : ℕ, f (i + η)‖ ≤ r * IntervalMat.expRemainderBound (r • A) η :=
    aux_norm_constTail_le A hr η hε ht0 htr
  intro j k
  -- each kept order stays inside the interval `constCorrTerm` spans
  have hfin : ∀ i ∈ Finset.range η,
      min (IntervalMat.constCorrTerm A r i j k) 0 ≤ (f i) j k
        ∧ (f i) j k ≤ max (IntervalMat.constCorrTerm A r i j k) 0 := by
    intro i _
    have hlow := IntervalMat.corrCoeff_le_sub (i := i + 2) (by omega) hs0
    have hupp := IntervalMat.sub_le_zero (i := i + 2) (by omega) hs0 hs1
    have hw : (f i) j k = ((t / r) ^ (i + 2) - (t / r))
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 1)) j k) := by
      simp only [hf, Matrix.smul_apply, smul_eq_mul, aux_pow_sub_eq hr]
      ring
    have hct : IntervalMat.constCorrTerm A r i j k = IntervalMat.corrCoeff (i + 2)
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 1)) j k) := by
      simp only [IntervalMat.constCorrTerm]
      ring
    rw [hw, hct]
    exact aux_mul_mem_minmax hlow hupp
  have hT : |(∑' i : ℕ, f (i + η)) j k| ≤ r * IntervalMat.expRemainderBound (r • A) η :=
    le_trans (abs_entry_le_norm _ j k) htail
  rw [abs_le] at hT
  rw [heq]
  simp only [Matrix.add_apply, Matrix.sum_apply, IntervalMat.constCorrectionMatrix]
  constructor
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).1
    linarith [hT.1]
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).2
    linarith [hT.2]

end CORALean.Real
