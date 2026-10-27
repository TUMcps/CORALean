module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrix
public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ExpRemainderBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsEntryLeNorm
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulMemMinmax
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowSubEq
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ScalarTermLe
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SubLeZero
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpDiff
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The interpolation error lies in the correction matrix

[1, Thm. 3]. Orders `2` through `η` are kept exactly, each contributing the interval between
`corrTerm` and zero (`corrCoeff` bounds `r^i (s^i - s)` for `t = s·r`); everything past `η` goes
into the remainder that bounds the exponential. The tail is not as tight: for
`E(t) = [-1,1]Φ(t)`, [1, Thm. 3] concludes `E(t) - (t/r)E(r) ⊆ E(r)` by pulling a *single*
`[-1,1]` out of both remainders; as independent interval matrices the difference has radius
`Φ(t) + (t/r)Φ(r)`, twice what `E(r)` allows at `t = r`. What holds (`ExpDiff`) is that the
remainders share `A^i` term by term: never splitting them leaves one series, and
`|t^i - t·r^(i-1)| ≤ r^i` bounds it by `∑_{i>η} ‖A‖^i r^i / i!`.

## Inputs
* `A` – system matrix
* `r` – step length
* `m` – Taylor order offset
* `t` – time

## Hypotheses
* `hr` – step length positive
* `hε` – scaled norm small enough for the Taylor order
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the interpolation error of the exponential lies in the correction matrix

## References

* [1] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". 2007 46th IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Opus 5
-- Written:       18-August-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- Every tail term is at most `r^m` in the scalar factor, so the tail is the
exponential's own remainder series. -/
private theorem aux_norm_expDiff_tail_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (η : ℕ)
    (hε : ‖r • A‖ / ((η : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    ‖∑' i : ℕ, (((Nat.factorial (i + (η + 1)) : ℝ))⁻¹
        * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1)))) • A ^ (i + (η + 1))‖
      ≤ MatExp.expRemainderBound (r • A) η := by -- --- PROOF ---
  -- the coefficient of the `i`-th term: a factorial and the interpolation error of `t ^ k`
  set c : ℕ → ℝ := fun i =>
    ((Nat.factorial (i + (η + 1)) : ℝ))⁻¹ * (t ^ (i + (η + 1)) - (t / r) * r ^ (i + (η + 1))) with
      hc
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  have hrA : ‖r • A‖ = r * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hcnn : (0:ℝ) ≤ ‖r • A‖ := norm_nonneg _
  have hε0 : (0:ℝ) ≤ ‖r • A‖ / ((η : ℝ) + 2) := by positivity
  -- each term is dominated by the exponential's own tail term
  have hterm : ∀ i : ℕ,
      ‖(c i) • A ^ (i + (η + 1))‖
        ≤ (‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
            * (‖r • A‖ / ((η : ℝ) + 2)) ^ i := by
    intro i
    set m := i + (η + 1) with hm
    have hscal : |t ^ m - (t / r) * r ^ m| ≤ r ^ m := by
      rw [pow_sub_eq hr m, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ m)]
      have h1 : |(t / r) ^ m - (t / r)| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [pow_nonneg hs0 m, pow_le_one₀ hs0 hs1 (n := m)]
        · nlinarith [pow_nonneg hs0 m, pow_le_one₀ hs0 hs1 (n := m)]
      nlinarith [pow_nonneg hr.le m]
    -- factorial, then the norm of the power, then the geometric form
    calc ‖(((Nat.factorial m : ℝ))⁻¹ * (t ^ m - (t / r) * r ^ m)) • A ^ m‖
        = |((Nat.factorial m : ℝ))⁻¹ * (t ^ m - (t / r) * r ^ m)| * ‖A ^ m‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ((Nat.factorial m : ℝ))⁻¹ * r ^ m * ‖A‖ ^ m := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((Nat.factorial m : ℝ))⁻¹)]
          gcongr
          · exact norm_pow_le' A (by omega)
      _ = ((Nat.factorial m : ℝ))⁻¹ * ‖r • A‖ ^ m := by rw [hrA, mul_pow]; ring
      _ ≤ _ := scalar_term_le hcnn η i
  -- `hε` is exactly what makes the comparison series geometric and convergent
  have hgeo : Summable (fun i : ℕ => (‖r • A‖ / ((η : ℝ) + 2)) ^ i) :=
    summable_geometric_of_lt_one hε0 hε
  have hnorm : Summable (fun i : ℕ =>
      ‖(c i) • A ^ (i + (η + 1))‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hterm (hgeo.mul_left _)
  -- norm of the sum under the sum of norms, then termwise, then in closed form
  calc ‖∑' i : ℕ, (c i) • A ^ (i + (η + 1))‖
      ≤ ∑' i : ℕ, ‖(c i) • A ^ (i + (η + 1))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i : ℕ, (‖r • A‖ ^ (η + 1) / Nat.factorial (η + 1))
          * (‖r • A‖ / ((η : ℝ) + 2)) ^ i :=
        Summable.tsum_le_tsum hterm hnorm (hgeo.mul_left _)
    _ = MatExp.expRemainderBound (r • A) η := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hε0 hε, MatExp.expRemainderBound]


-- =======================================  MAIN THEOREM  ======================================= --

theorem MatExp.expDiff_mem_correctionMatrix (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) {m : ℕ}
    (hε : ‖r • A‖ / (((m + 2 : ℕ) : ℝ) + 2) < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (htr : t ≤ r) : -- --- CONCL ---
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      ∈ (MatExp.correctionMatrix A r (m + 2)).construct := by -- --- PROOF ---
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
      simp only [hf, Matrix.smul_apply, smul_eq_mul, pow_sub_eq hr]
      ring
    have hct : MatExp.corrTerm A r (i + 2) j k = MatExp.corrCoeff (i + 2)
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 2)) j k) := by
      simp only [MatExp.corrTerm]
      ring
    rw [hw, hct]
    exact mul_mem_minmax hlow hupp
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


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
