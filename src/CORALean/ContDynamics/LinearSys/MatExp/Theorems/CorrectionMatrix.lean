import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpEnclosure

/-!
# The interpolation error lies in the correction matrix

Althoff's thesis (2010), Prop. 3.1. Orders `2` through `η` are kept exactly,
each contributing the interval between `corrTerm` and zero; everything past `η`
goes into the same remainder that bounds the exponential.

Substituting `t = s·r` turns order `i` into `r^i (s^i - s)`, which `corrCoeff`
bounds exactly — so the finite part is as tight as the thesis claims.

## Why the tail is bounded as one series

The proposition is true as stated and the finite part is proved as the thesis
proves it, but the tail argument is not the thesis's. For `Φ(t)` the scalar tail
bound and `E(t) = [-1,1]Φ(t)`, the thesis concludes
`E(t) - (t/r)E(r) = [-1,1](Φ(t) - (t/r)Φ(r)) ⊆ E(r)` — pulling a *single*
`[-1,1]` out of both remainders. Read as two independent interval matrices, the
standard reading, that difference has radius `Φ(t) + (t/r)Φ(r)`, twice what
`E(r)` allows at `t = r`.

What does hold, and what `ExpDiff` sets up, is that the two remainders share
`A^i` term by term. Never splitting them leaves one series, and for `0 ≤ t ≤ r`
`|t^i - t·r^(i-1)| = t·(r^(i-1) - t^(i-1)) ≤ r^i`, so the tail is dominated by
`∑_{i>η} ‖A‖^i r^i / i!` — the proposition's own bound, with no dependency
assumed. CORA's `manual/complementary` `Documentation/inputErrorBounds` argues
the integrated remainder `Ê` the same way.
-/

-- Authors:       Tobias Ladner
-- Written:       18-August-2026
-- Last update:   ---
-- Last revision: ---

namespace CORALean.Real

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
      ≤ MatExp.expRemainderBound (r • A) η := by
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
    _ = MatExp.expRemainderBound (r • A) η := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε, MatExp.expRemainderBound]

set_option maxHeartbeats 1000000 in
theorem MatExp.expDiff_mem_correctionMatrix (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) :
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      ∈ (MatExp.correctionMatrix A r (m + 2)).construct := by
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  set f : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + 2) : ℝ))⁻¹ * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 2)
    with hf
  have hsum : Summable f := MatExp.summable_expDiff A t r
  have hsplit := hsum.sum_add_tsum_nat_add (m + 1)
  have heq : exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      = (∑ i ∈ Finset.range (m + 1), f i) + ∑' i : ℕ, f (i + (m + 1)) := by
    rw [MatExp.expDiff_eq_tsum A t r hr.ne', ← hsplit]
  have htail := aux_norm_expDiff_tail_le A hr (m + 2) hε ht0 htr
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  -- each order between `2` and `η` stays inside the interval `corrTerm` spans
  have hfin : ∀ i ∈ Finset.range (m + 1),
      min (MatExp.corrTerm A r (i + 2) j k) 0 ≤ (f i) j k
        ∧ (f i) j k ≤ max (MatExp.corrTerm A r (i + 2) j k) 0 := by
    intro i _
    have hlow := MatExp.corrCoeff_le_sub (i := i + 2) (by omega) hs0
    have hupp := MatExp.sub_le_zero (i := i + 2) (by omega) hs0 hs1
    have hw : (f i) j k = ((t / r) ^ (i + 2) - (t / r))
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 2)) j k) := by
      simp only [hf, Matrix.smul_apply, smul_eq_mul, aux_pow_sub_eq hr]
      ring
    have hct : MatExp.corrTerm A r (i + 2) j k = MatExp.corrCoeff (i + 2)
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 2)) j k) := by
      simp only [MatExp.corrTerm]
      ring
    rw [hw, hct]
    exact aux_mul_mem_minmax hlow hupp
  -- the tail is inside the remainder, entrywise because an entry never exceeds the norm
  have hT : |(∑' i : ℕ, f (i + (m + 1))) j k|
      ≤ MatExp.expRemainderBound (r • A) (m + 2) :=
    le_trans (abs_entry_le_norm _ j k) htail
  rw [abs_le] at hT
  rw [heq]
  simp only [Matrix.add_apply, Matrix.sum_apply, MatExp.correctionMatrix,
    show m + 2 - 1 = m + 1 from rfl]
  constructor
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).1
    linarith [hT.1]
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).2
    linarith [hT.2]

end CORALean.Real
