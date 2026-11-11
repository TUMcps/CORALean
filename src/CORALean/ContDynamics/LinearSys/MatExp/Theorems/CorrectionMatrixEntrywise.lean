module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.CorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpDiff
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulMemMinmax
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowSubEq
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SubLeZero
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpDiff
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The interpolation error lies in CORA's correction matrix

The tail of `expDiff_mem_correctionMatrix` [2, Thm. 3] against the entrywise remainder of [1]
instead of the scalar bound: the `i`-th tail term of the interpolation error is
`(t^i - (t/r) r^i)/i! · Aⁱ`, and `|t^i - (t/r) r^i| ≤ r^i` and `|Aⁱ| ≤ |A|ⁱ` entrywise put it
under the `i`-th term of `E(r,η)`. Nothing is asked of `η`: the entrywise remainder is the sum of
the series itself, with no geometric bound behind it.

## Inputs
* `A` – system matrix
* `r` – step length
* `m` – Taylor order offset
* `t` – time

## Hypotheses
* `hr` – step length positive
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the interpolation error of the exponential lies in the entrywise correction matrix

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
* [2] [M. Althoff, O. Stursberg and M. Buss. "Reachability Analysis of Linear Systems with Uncertain
      Parameters and Inputs". Proceedings of the IEEE Conference on Decision and Control,
      2007.](../../../../../../references/2007/althoff-cdc-uncertain-parameters-inputs.md)
-/

-- Authors:       Claude Sonnet 5.5
-- Written:       11-November-2026
-- Last update:   ---
-- Reviewed:      ---


-- ----------------------------------------  BEGIN CODE  ---------------------------------------- --

namespace CORALean.Real

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}


-- ----------------------------------------  AUXILIARY  ----------------------------------------- --

/-- The tail of the interpolation error, past order `N + 1`, is entrywise under `E(r, N + 1)`. -/
private theorem aux_tail_entry_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (N : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (j k : Fin n) : -- --- CONCL ---
    |(∑' i : ℕ, (((Nat.factorial (i + N + 2) : ℝ))⁻¹
        * (t ^ (i + N + 2) - (t / r) * r ^ (i + N + 2))) • A ^ (i + N + 2)) j k|
      ≤ MatExp.expRemainderMat A r (N + 1) j k := by -- --- PROOF ---
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  set f : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + N + 2) : ℝ))⁻¹ * (t ^ (i + N + 2) - (t / r) * r ^ (i + N + 2)))
      • A ^ (i + N + 2) with hf
  have hsum : Summable f := by
    have h := (summable_nat_add_iff N).mpr (MatExp.summable_expDiff A t r)
    exact h.congr fun i => by simp only [hf, add_assoc]
  -- the `i`-th term of `E(r, N + 1)`, entry `(j, k)`
  have hE := MatExp.hasSum_expRemainderMat_entry A r (N + 1) j k
  have hdom : ∀ i : ℕ, ‖(f i) j k‖ ≤ (((Nat.factorial (i + (N + 1 + 1)) : ℝ)⁻¹
      * r ^ (i + (N + 1 + 1))) • (MatExp.absMat A) ^ (i + (N + 1 + 1))) j k := by
    intro i
    have e : i + (N + 1 + 1) = i + N + 2 := by omega
    rw [e, Real.norm_eq_abs]
    -- the scalar factor is under `r^{i+N+2}`
    have hscal : |t ^ (i + N + 2) - (t / r) * r ^ (i + N + 2)| ≤ r ^ (i + N + 2) := by
      rw [pow_sub_eq hr (i + N + 2), abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (i + N + 2))]
      have h1 : |(t / r) ^ (i + N + 2) - (t / r)| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [pow_nonneg hs0 (i + N + 2), pow_le_one₀ hs0 hs1 (n := i + N + 2)]
        · nlinarith [pow_nonneg hs0 (i + N + 2), pow_le_one₀ hs0 hs1 (n := i + N + 2)]
      nlinarith [pow_nonneg hr.le (i + N + 2)]
    -- the entry is a product of the scalar factors and the matrix entry
    have hfp : (0:ℝ) ≤ ((Nat.factorial (i + N + 2) : ℝ))⁻¹ := by positivity
    simp only [hf, Matrix.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg hfp]
    -- each factor is under the matching one of the remainder's term
    calc ((Nat.factorial (i + N + 2) : ℝ))⁻¹
          * |t ^ (i + N + 2) - (t / r) * r ^ (i + N + 2)| * |(A ^ (i + N + 2)) j k|
        ≤ ((Nat.factorial (i + N + 2) : ℝ))⁻¹ * r ^ (i + N + 2)
            * ((MatExp.absMat A) ^ (i + N + 2)) j k := by
          gcongr
          exact abs_pow_entry_le_absMat_pow_entry A _ j k
      _ = _ := by ring
  have hnormsum : Summable fun i => ‖(f i) j k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hE.summable
  have hcs : Summable fun i => (f i) j k :=
    Summable.of_norm hnormsum
  rw [MatExp.tsum_entry_eq hsum j k]
  have := tsum_of_norm_bounded hE hdom
  simpa only [Real.norm_eq_abs] using this


-- =======================================  MAIN THEOREM  ======================================= --

/-- The interpolation error of the exponential lies in `F` of CORA, whatever the order. -/
theorem MatExp.expDiff_mem_correctionMatrixEntrywise (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    exp (t • A) - 1 - (t / r) • (exp (r • A) - 1)
      ∈ (MatExp.correctionMatrixEntrywise A r (m + 2)).toSet := by -- --- PROOF ---
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
  -- the tail is inside the entrywise remainder
  have hT : |(∑' i : ℕ, f (i + (m + 1))) j k| ≤ MatExp.expRemainderMat A r (m + 2) j k := by
    have h := aux_tail_entry_le A hr (m + 1) ht0 htr j k
    simpa only [hf, add_assoc, show m + 1 + 1 = m + 2 from rfl] using h
  rw [abs_le] at hT
  rw [heq]
  simp only [Matrix.add_apply, Matrix.sum_apply, MatExp.correctionMatrixEntrywise,
    show m + 2 - 1 = m + 1 from rfl]
  constructor
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).1
    linarith [hT.1]
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).2
    linarith [hT.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
