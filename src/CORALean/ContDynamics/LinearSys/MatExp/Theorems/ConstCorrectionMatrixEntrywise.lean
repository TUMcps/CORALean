module

public import CORALean.ContDynamics.LinearSys.MatExp.Operations.ConstCorrectionMatrixEntrywise
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.AbsPowEntryLeAbsMatPow
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.CorrCoeffBound
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.ExpIntegralDiffEqTsum
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.HasSumExpRemainderMatEntry
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.MulMemMinmax
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.PowSubEq
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SubLeZero
public import CORALean.ContDynamics.LinearSys.MatExp.Theorems.SummableExpIntegralDiff
public import CORALean.ContSet.Interval.Real.Theorems.MemMat

@[expose] public section

/-!
# The constant input's interpolation error lies in CORA's `G`

The tail of `expIntegralDiff_mem_constCorrectionMatrix` [2, Sec. III-A] against the entrywise
remainder of [1] instead of the scalar bound: the `i`-th tail term of the interpolation error is
`(t^{i+2} - (t/r) r^{i+2})/(i+2)! · A^{i+1}`; with `|t^{i+2} - (t/r) r^{i+2}| ≤ r^{i+2}`, `|A^{i+1}|
≤ |A|^{i+1}` and `(i+2)! ≥ (i+1)!` it is under `r` times the `i`-th term of `E(r,η)`. Nothing is
asked of `η`.

## Inputs
* `A` – system matrix
* `r` – step length
* `η` – Taylor order
* `t` – time

## Hypotheses
* `hr` – step length positive
* `ht0` – time nonnegative
* `htr` – time within the step

## Conclusion
* the constant input's interpolation error lies in the entrywise integrated correction matrix

## References

* [1] [M. Wetzlinger, N. Kochdumper, S. Bak and M. Althoff. "Fully-Automated Verification of Linear
      Systems Using Inner- and Outer-Approximations of Reachable Sets". IEEE Transactions on
      Automatic Control,
      2023.](../../../../../../references/2023/wetzlinger-fully-automated-verification.md)
* [2] [M. Althoff and B. H. Krogh. "Reachability Analysis of Nonlinear Differential-Algebraic
      Systems". IEEE Transactions on Automatic Control,
      2014.](../../../../../../references/2014/althoff-tac-nonlinear-dae.md)
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

/-- The tail of the interpolation error, from order `η`, is entrywise under `r · E(r, η)`. -/
private theorem aux_tail_entry_le (A : Mat ℝ n n) {r : ℝ} (hr : 0 < r) (η : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (htr : t ≤ r) (j k : Fin n) : -- --- CONCL ---
    |(∑' i : ℕ, (((Nat.factorial (i + η + 2) : ℝ))⁻¹
        * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2))) • A ^ (i + η + 1)) j k|
      ≤ r * MatExp.expRemainderMat A r η j k := by -- --- PROOF ---
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  set f : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + η + 2) : ℝ))⁻¹ * (t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2)))
      • A ^ (i + η + 1) with hf
  have hsum : Summable f := by
    have h := (summable_nat_add_iff η).mpr (MatExp.summable_expIntegralDiff A t r)
    exact h.congr fun i => by simp only [hf, add_assoc]
  have hE := (MatExp.hasSum_expRemainderMat_entry A r η j k).mul_left r
  have hdom : ∀ i : ℕ, ‖(f i) j k‖ ≤ r * ((((Nat.factorial (i + (η + 1)) : ℝ)⁻¹
      * r ^ (i + (η + 1))) • (MatExp.absMat A) ^ (i + (η + 1))) j k) := by
    intro i
    have e : i + (η + 1) = i + η + 1 := by omega
    rw [e, Real.norm_eq_abs]
    -- the scalar factor is under `r^{i+η+2}`
    have hscal : |t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2)| ≤ r ^ (i + η + 2) := by
      rw [pow_sub_eq hr (i + η + 2), abs_mul,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ (i + η + 2))]
      have h1 : |(t / r) ^ (i + η + 2) - (t / r)| ≤ 1 := by
        rw [abs_le]
        constructor
        · nlinarith [pow_nonneg hs0 (i + η + 2), pow_le_one₀ hs0 hs1 (n := i + η + 2)]
        · nlinarith [pow_nonneg hs0 (i + η + 2), pow_le_one₀ hs0 hs1 (n := i + η + 2)]
      nlinarith [pow_nonneg hr.le (i + η + 2)]
    -- the factorial is one step larger than the remainder's, so its inverse is smaller
    have hfp : (0:ℝ) ≤ ((Nat.factorial (i + η + 2) : ℝ))⁻¹ := by positivity
    have hfle : ((Nat.factorial (i + η + 2) : ℝ))⁻¹ ≤ ((Nat.factorial (i + η + 1) : ℝ))⁻¹ :=
      inv_anti₀ (by exact_mod_cast Nat.factorial_pos _)
        (by exact_mod_cast Nat.factorial_le (by omega))
    -- the entry is a product of the two scalar factors and the matrix entry
    simp only [hf, Matrix.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg hfp]
    -- the power's entry is under the entry of the power of `|A|`
    have hpow : |(A ^ (i + η + 1)) j k| ≤ ((MatExp.absMat A) ^ (i + η + 1)) j k :=
      abs_pow_entry_le_absMat_pow_entry A _ j k
    have hBnn : 0 ≤ ((MatExp.absMat A) ^ (i + η + 1)) j k := le_trans (abs_nonneg _) hpow
    calc ((Nat.factorial (i + η + 2) : ℝ))⁻¹
          * |t ^ (i + η + 2) - (t / r) * r ^ (i + η + 2)| * |(A ^ (i + η + 1)) j k|
        ≤ ((Nat.factorial (i + η + 1) : ℝ))⁻¹ * r ^ (i + η + 2)
            * ((MatExp.absMat A) ^ (i + η + 1)) j k := by
          gcongr
      _ = _ := by ring
  have hnormsum : Summable fun i => ‖(f i) j k‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hE.summable
  rw [MatExp.tsum_entry_eq hsum j k]
  have := tsum_of_norm_bounded hE hdom
  simpa only [Real.norm_eq_abs] using this


-- =======================================  MAIN THEOREM  ======================================= --

/-- The constant input's interpolation error lies in `G` of CORA, whatever the order. -/
theorem MatExp.expIntegralDiff_mem_constCorrectionMatrixEntrywise (A : Mat ℝ n n) {r : ℝ}
    (hr : 0 < r) (η : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r) : -- --- CONCL ---
    MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r
      ∈ (MatExp.constCorrectionMatrixEntrywise A r η).toSet := by -- --- PROOF ---
  have hs0 : 0 ≤ t / r := div_nonneg ht0 hr.le
  have hs1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  set f : ℕ → Mat ℝ n n := fun i =>
    (((Nat.factorial (i + 2) : ℝ))⁻¹ * (t ^ (i + 2) - (t / r) * r ^ (i + 2))) • A ^ (i + 1)
    with hf
  have hsum : Summable f := MatExp.summable_expIntegralDiff A t r
  have hsplit := hsum.sum_add_tsum_nat_add η
  have heq : MatExp.expIntegral A t - (t / r) • MatExp.expIntegral A r
      = (∑ i ∈ Finset.range η, f i) + ∑' i : ℕ, f (i + η) := by
    rw [MatExp.expIntegralDiff_eq_tsum A t r hr.ne', ← hsplit]
  refine Interval.mem_mat_iff.mpr fun j k => ?_
  -- each kept order stays inside the interval `constCorrTerm` spans
  have hfin : ∀ i ∈ Finset.range η,
      min (MatExp.constCorrTerm A r i j k) 0 ≤ (f i) j k
        ∧ (f i) j k ≤ max (MatExp.constCorrTerm A r i j k) 0 := by
    intro i _
    have hlow := MatExp.corrCoeff_le_sub (i := i + 2) (by omega) hs0
    have hupp := MatExp.sub_le_zero (i := i + 2) (by omega) hs0 hs1
    have hw : (f i) j k = ((t / r) ^ (i + 2) - (t / r))
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 1)) j k) := by
      simp only [hf, Matrix.smul_apply, smul_eq_mul, pow_sub_eq hr]
      ring
    have hct : MatExp.constCorrTerm A r i j k = MatExp.corrCoeff (i + 2)
        * (((Nat.factorial (i + 2) : ℝ))⁻¹ * r ^ (i + 2) * (A ^ (i + 1)) j k) := by
      simp only [MatExp.constCorrTerm]
      ring
    rw [hw, hct]
    exact mul_mem_minmax hlow hupp
  -- the tail is inside `E(r,η)·r`, entry by entry
  have hT : |(∑' i : ℕ, f (i + η)) j k| ≤ r * MatExp.expRemainderMat A r η j k := by
    have h := aux_tail_entry_le A hr η ht0 htr j k
    simpa only [hf, add_assoc] using h
  rw [abs_le] at hT
  rw [heq]
  simp only [Matrix.add_apply, Matrix.sum_apply, MatExp.constCorrectionMatrixEntrywise]
  constructor
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).1
    linarith [hT.1]
  · have := Finset.sum_le_sum fun i hi => (hfin i hi).2
    linarith [hT.2]

end CORALean.Real


-- ---------------------------------------  END OF CODE  ---------------------------------------- --
